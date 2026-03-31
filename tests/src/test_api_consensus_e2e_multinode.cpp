#include <cy_platform.h>
#include <rapidhash.h>
#include <unity.h>
#include "e2e_faults.hpp"
#include "e2e_sim_net.hpp"
#include "e2e_scenario_utils.hpp"
#include "e2e_test_utils.hpp"
#include "helpers.h"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>

namespace {

constexpr cy_us_t step_us             = 10'000;
constexpr cy_us_t publish_deadline_us = 300'000;

using e2e::arrival_capture_t;
using e2e::arrival_sample_t;
using e2e::count_by_publisher;
using e2e::on_arrival_capture;

constexpr std::array<const char*, 3> colliding_topics = {
    "e2e/migrate/alpha_0",
    "e2e/migrate/beta_14014",
    "e2e/migrate/gamma_67275",
};

cy_err_t publish_best_effort(cy_publisher_t* const pub,
                             const std::uint32_t   publisher_id,
                             const std::uint64_t   sequence,
                             const cy_us_t         now)
{
    const auto       payload = e2e::app_payload_pack(publisher_id, sequence);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    return cy_publish(pub, now + publish_deadline_us, msg);
}

std::size_t count_from_publisher_topic(const arrival_capture_t& capture,
                                       const std::uint32_t      publisher_id,
                                       const std::uint64_t      topic_hash)
{
    const auto count =
      std::ranges::count_if(capture.samples, [publisher_id, topic_hash](const arrival_sample_t& sample) {
          return (sample.publisher_id == publisher_id) && (sample.topic_hash == topic_hash);
      });
    return static_cast<std::size_t>(count);
}

std::size_t count_pub_frames_for_hash(const std::vector<e2e::frame_capture_t>& captures, const std::uint64_t topic_hash)
{
    const auto count = std::ranges::count_if(captures, [topic_hash](const e2e::frame_capture_t& cap) {
        return cap.frame.has_topic_hash && (cap.frame.topic_hash == topic_hash) &&
               ((cap.frame.header_type == 0U) || (cap.frame.header_type == 1U));
    });
    return static_cast<std::size_t>(count);
}

std::uint64_t mix_hash(std::uint64_t h, const std::uint64_t x)
{
    h ^= x + UINT64_C(0x9E3779B97F4A7C15) + (h << 6U) + (h >> 2U);
    return h;
}

std::uint64_t capture_fingerprint(const e2e::frame_capture_t& cap)
{
    std::uint64_t h = UINT64_C(0xCBF29CE484222325);
    h               = mix_hash(h, cap.frame.sequence);
    h               = mix_hash(h, cap.frame.source);
    h               = mix_hash(h, cap.frame.destination);
    h               = mix_hash(h, cap.frame.unicast ? 1U : 0U);
    h               = mix_hash(h, cap.frame.subject_id);
    h               = mix_hash(h, cap.frame.priority);
    h               = mix_hash(h, static_cast<std::uint64_t>(cap.frame.send_time));
    h               = mix_hash(h, static_cast<std::uint64_t>(cap.frame.deliver_time));
    h               = mix_hash(h, cap.frame.header_type);
    h               = mix_hash(h, cap.frame.has_tag ? cap.frame.tag : 0U);
    h               = mix_hash(h, cap.frame.has_topic_hash ? cap.frame.topic_hash : 0U);
    h               = mix_hash(h, cap.dropped ? 1U : 0U);
    h               = mix_hash(h, cap.copy_index);
    h               = mix_hash(h, cap.frame.wire.size());
    for (std::size_t i = 0U; i < std::min<std::size_t>(16U, cap.frame.wire.size()); i++) {
        h = mix_hash(h, cap.frame.wire.at(i));
    }
    return h;
}

std::uint32_t pub_id_for(const std::size_t node_index) { return static_cast<std::uint32_t>(6000U + node_index); }

std::uint32_t pub_id_for_topic(const std::size_t node_index, const std::size_t topic_index)
{
    return static_cast<std::uint32_t>(7000U + (topic_index * 100U) + node_index);
}

std::optional<std::uint32_t> last_subject_for_hash(const std::vector<e2e::frame_capture_t>& captures,
                                                   const std::size_t                        src_node,
                                                   const std::uint64_t                      topic_hash)
{
    for (std::size_t i = captures.size(); i > 0U; i--) {
        const e2e::frame_capture_t& cap = captures.at(i - 1U);
        if ((cap.frame.source == src_node) && (cap.frame.has_topic_hash) && (cap.frame.topic_hash == topic_hash) &&
            ((cap.frame.header_type == 0U) || (cap.frame.header_type == 1U))) {
            return cap.frame.subject_id;
        }
    }
    return std::nullopt;
}

std::optional<std::uint32_t> last_subject_for_hash_any(const std::vector<e2e::frame_capture_t>& captures,
                                                       const std::uint64_t                      topic_hash)
{
    for (std::size_t i = captures.size(); i > 0U; i--) {
        const e2e::frame_capture_t& cap = captures.at(i - 1U);
        if (cap.frame.has_topic_hash && (cap.frame.topic_hash == topic_hash) &&
            ((cap.frame.header_type == 0U) || (cap.frame.header_type == 1U))) {
            return cap.frame.subject_id;
        }
    }
    return std::nullopt;
}

void inject_divergent_gossip(e2e::sim_net_t&     net,
                             const std::size_t   dst_node,
                             const std::uint64_t remote_id,
                             const std::uint64_t topic_hash,
                             const std::uint32_t evictions,
                             const char* const   topic_name,
                             const cy_us_t       now)
{
    std::array<unsigned char, 256> wire{};
    const std::size_t              size =
      make_gossip_header(wire.data(), wire.size(), 3U, 0, topic_hash, evictions, cy_str(topic_name));
    TEST_ASSERT_TRUE(size > 0U);

    auto* const         heap = &e2e::sim_net_message_heap(net, dst_node);
    cy_message_t* const msg  = cy_test_message_make(heap, wire.data(), size);
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t mts{};
    mts.timestamp = now;
    mts.content   = msg;

    cy_lane_t lane{};
    lane.id           = remote_id;
    lane.prio         = cy_prio_nominal;
    lane.ctx.state[0] = static_cast<unsigned char>(remote_id & 0xFFU);

    cy_on_message(e2e::sim_net_platform(net, dst_node), lane, nullptr, mts);
}

struct one_topic_env_t final
{
    e2e::sim_net_t                 net{};
    std::vector<cy_publisher_t*>   pubs{};
    std::vector<cy_future_t*>      subs{};
    std::vector<arrival_capture_t> captures{};
    std::vector<std::uint64_t>     next_seq{};
};

void one_topic_init(one_topic_env_t&                  env,
                    const std::size_t                 node_count,
                    const std::uint64_t               seed,
                    const char* const                 topic_name,
                    const e2e::fault_plan_t* const    frame_faults = nullptr,
                    const e2e::op_fault_plan_t* const op_faults    = nullptr)
{
    e2e::sim_net_config_t cfg{};
    cfg.node_count         = node_count;
    cfg.random_seed_base   = seed;
    cfg.subject_id_modulus = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit);
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(env.net, cfg));
    e2e::sim_net_faults_set(env.net, frame_faults, op_faults);

    env.pubs.assign(node_count, nullptr);
    env.subs.assign(node_count, nullptr);
    env.captures.assign(node_count, arrival_capture_t{});
    env.next_seq.assign(node_count, 0U);

    for (std::size_t i = 0U; i < node_count; i++) {
        cy_future_t* const sub = cy_subscribe(e2e::sim_net_cy(env.net, i), cy_str(topic_name), 64U);
        TEST_ASSERT_NOT_NULL(sub);
        env.subs.at(i) = sub;

        cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
        ctx.ptr[0]            = &env.captures.at(i);
        cy_future_context_set(sub, ctx);
        cy_future_callback_set(sub, on_arrival_capture);

        cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(env.net, i), cy_str(topic_name));
        TEST_ASSERT_NOT_NULL(pub);
        env.pubs.at(i) = pub;
    }
}

void one_topic_publish_round(one_topic_env_t& env, const cy_us_t now)
{
    for (std::size_t i = 0U; i < env.pubs.size(); i++) {
        const std::uint32_t pub_id = pub_id_for(i);
        const std::uint64_t seq    = ++env.next_seq.at(i);
        const cy_err_t      err    = publish_best_effort(env.pubs.at(i), pub_id, seq, now);
        TEST_ASSERT_TRUE((err == CY_OK) || (err == CY_ERR_MEDIA));
    }
}

void one_topic_assert_reachability(const one_topic_env_t& env)
{
    for (const arrival_capture_t& capture : env.captures) {
        TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    }
    for (std::size_t receiver = 0U; receiver < env.captures.size(); receiver++) {
        for (std::size_t sender = 0U; sender < env.captures.size(); sender++) {
            if (receiver == sender) {
                continue;
            }
            TEST_ASSERT_TRUE(count_by_publisher(env.captures.at(receiver), pub_id_for(sender)) > 0U);
        }
    }
}

void one_topic_cleanup(one_topic_env_t& env, cy_us_t& now)
{
    e2e::sim_net_faults_set(env.net, nullptr, nullptr);

    for (cy_future_t* const sub : env.subs) {
        if (sub != nullptr) {
            cy_future_destroy(sub);
        }
    }
    e2e::drive_for_all(env.net, now, 80'000, step_us, false);

    for (cy_publisher_t* const pub : env.pubs) {
        if (pub != nullptr) {
            cy_unadvertise(pub);
        }
    }
    e2e::drive_for_all(env.net, now, 80'000, step_us, false);

    e2e::drain_queue_all(env.net, now, step_us, 80'000U);
    e2e::assert_quiescent(env.net);

    e2e::sim_net_deinit(env.net);
    e2e::assert_all_node_heaps_clean(env.net);
    e2e::assert_no_live_messages();
}

void test_api_consensus_e2e_m01_five_node_baseline_convergence()
{
    one_topic_env_t env{};
    one_topic_init(env, 5U, UINT64_C(0xA010), "e2e/multi/m01/topic");
    cy_us_t now = 0;

    for (std::size_t round = 0U; round < 32U; round++) {
        e2e::set_now_all(env.net, now);
        one_topic_publish_round(env, now);
        e2e::drive_for_all(env.net, now, 20'000, step_us, false);
    }
    e2e::drive_for_all(env.net, now, 250'000, step_us, false);

    one_topic_assert_reachability(env);
    one_topic_cleanup(env, now);
}

void test_api_consensus_e2e_m02_split_partition_heal_eventual_delivery()
{
    constexpr cy_us_t partition_end = 220'000;
    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        if (frame.send_time > partition_end) {
            return false;
        }
        const bool in_left_src = frame.source < 2U;
        const bool in_left_dst = frame.destination < 2U;
        return in_left_src != in_left_dst;
    });

    one_topic_env_t env{};
    one_topic_init(env, 5U, UINT64_C(0xA020), "e2e/multi/m02/topic", &faults);
    cy_us_t now = 0;

    for (std::size_t round = 0U; round < 40U; round++) {
        e2e::set_now_all(env.net, now);
        one_topic_publish_round(env, now);
        e2e::drive_for_all(env.net, now, 20'000, step_us, false);
    }
    e2e::drive_for_all(env.net, now, 300'000, step_us, false);

    one_topic_assert_reachability(env);
    one_topic_cleanup(env, now);
}

void test_api_consensus_e2e_m03_bridge_node_isolation_then_restore()
{
    constexpr std::size_t bridge_node   = 2U;
    constexpr cy_us_t     isolation_end = 220'000;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        return (frame.send_time <= isolation_end) &&
               ((frame.source == bridge_node) || (frame.destination == bridge_node));
    });

    one_topic_env_t env{};
    one_topic_init(env, 5U, UINT64_C(0xA030), "e2e/multi/m03/topic", &faults);
    cy_us_t now = 0;

    for (std::size_t round = 0U; round < 44U; round++) {
        e2e::set_now_all(env.net, now);
        one_topic_publish_round(env, now);
        e2e::drive_for_all(env.net, now, 20'000, step_us, false);
    }
    e2e::drive_for_all(env.net, now, 320'000, step_us, false);

    one_topic_assert_reachability(env);
    one_topic_cleanup(env, now);
}

std::uint8_t rotating_group(const cy_us_t time, const std::size_t node)
{
    if (time < 180'000) {
        return (node < 2U) ? 0U : 1U;
    }
    if (time < 360'000) {
        return ((node == 0U) || (node == 2U)) ? 0U : 1U;
    }
    if (time < 540'000) {
        return ((node == 1U) || (node == 3U)) ? 0U : 1U;
    }
    return 0U;
}

void test_api_consensus_e2e_m04_rotating_partitions_eventual_recovery()
{
    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        if (frame.send_time >= 540'000) {
            return false;
        }
        return rotating_group(frame.send_time, frame.source) != rotating_group(frame.send_time, frame.destination);
    });

    one_topic_env_t env{};
    one_topic_init(env, 5U, UINT64_C(0xA040), "e2e/multi/m04/topic", &faults);
    cy_us_t now = 0;

    for (std::size_t round = 0U; round < 56U; round++) {
        e2e::set_now_all(env.net, now);
        one_topic_publish_round(env, now);
        e2e::drive_for_all(env.net, now, 20'000, step_us, false);
    }
    e2e::drive_for_all(env.net, now, 400'000, step_us, false);

    one_topic_assert_reachability(env);
    one_topic_cleanup(env, now);
}

void test_api_consensus_e2e_m05_three_colliding_topics_subject_uniqueness()
{
    e2e::sim_net_config_t cfg{};
    cfg.node_count       = 5U;
    cfg.random_seed_base = UINT64_C(0xA050);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    std::vector<arrival_capture_t>            captures(cfg.node_count);
    std::vector<std::vector<cy_future_t*>>    subs(cfg.node_count,
                                                std::vector<cy_future_t*>(colliding_topics.size(), nullptr));
    std::vector<std::vector<cy_publisher_t*>> pubs(cfg.node_count,
                                                   std::vector<cy_publisher_t*>(colliding_topics.size(), nullptr));
    std::vector<std::vector<std::uint64_t>>   seq(cfg.node_count,
                                                std::vector<std::uint64_t>(colliding_topics.size(), 0U));

    for (std::size_t node = 0U; node < cfg.node_count; node++) {
        for (std::size_t topic = 0U; topic < colliding_topics.size(); topic++) {
            subs.at(node).at(topic) = cy_subscribe(e2e::sim_net_cy(net, node), cy_str(colliding_topics.at(topic)), 64U);
            TEST_ASSERT_NOT_NULL(subs.at(node).at(topic));
            cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
            ctx.ptr[0]            = &captures.at(node);
            cy_future_context_set(subs.at(node).at(topic), ctx);
            cy_future_callback_set(subs.at(node).at(topic), on_arrival_capture);

            pubs.at(node).at(topic) = cy_advertise(e2e::sim_net_cy(net, node), cy_str(colliding_topics.at(topic)));
            TEST_ASSERT_NOT_NULL(pubs.at(node).at(topic));
        }
    }

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, 700'000, step_us, false);

    std::array<std::uint64_t, colliding_topics.size()> hashes{};
    for (std::size_t topic = 0U; topic < colliding_topics.size(); topic++) {
        const cy_topic_t* const t = cy_topic_find_by_name(e2e::sim_net_cy(net, 0U), cy_str(colliding_topics.at(topic)));
        TEST_ASSERT_NOT_NULL(t);
        hashes.at(topic) = cy_topic_hash(t);
    }

    for (std::size_t round = 0U; round < 24U; round++) {
        e2e::set_now_all(net, now);
        for (std::size_t node = 0U; node < cfg.node_count; node++) {
            for (std::size_t topic = 0U; topic < colliding_topics.size(); topic++) {
                const cy_err_t err = publish_best_effort(
                  pubs.at(node).at(topic), pub_id_for_topic(node, topic), ++seq.at(node).at(topic), now);
                TEST_ASSERT_EQUAL_INT(CY_OK, err);
            }
        }
        e2e::drive_for_all(net, now, 20'000, step_us, false);
    }
    e2e::drive_for_all(net, now, 280'000, step_us, false);

    for (const arrival_capture_t& capture : captures) {
        TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    }

    for (std::size_t sender = 0U; sender < cfg.node_count; sender++) {
        for (std::size_t topic = 0U; topic < colliding_topics.size(); topic++) {
            std::size_t receivers_with_samples = 0U;
            for (std::size_t receiver = 0U; receiver < cfg.node_count; receiver++) {
                if (receiver == sender) {
                    continue;
                }
                if (count_from_publisher_topic(
                      captures.at(receiver), pub_id_for_topic(sender, topic), hashes.at(topic)) > 0U) {
                    receivers_with_samples++;
                }
            }
            if (receivers_with_samples == 0U) {
                const std::string msg = "m05 sender=" + std::to_string(sender) +
                                        " topic_index=" + std::to_string(topic) +
                                        " pub_id=" + std::to_string(pub_id_for_topic(sender, topic)) +
                                        " topic_hash=" + std::to_string(hashes.at(topic));
                TEST_FAIL_MESSAGE(msg.c_str());
            }
        }
    }

    std::set<std::uint32_t> final_subjects{};
    for (std::size_t topic = 0U; topic < colliding_topics.size(); topic++) {
        std::optional<std::uint32_t> reference{};
        for (std::size_t node = 0U; node < cfg.node_count; node++) {
            const auto subject = last_subject_for_hash(e2e::sim_net_captures(net), node, hashes.at(topic));
            TEST_ASSERT_TRUE(subject.has_value());
            if (!reference.has_value()) {
                reference = subject;
            }
            TEST_ASSERT_EQUAL_UINT32(*reference, *subject);
        }
        final_subjects.insert(*reference);
    }
    TEST_ASSERT_EQUAL_size_t(colliding_topics.size(), final_subjects.size());

    e2e::sim_net_faults_set(net, nullptr, nullptr);
    for (const auto& row : subs) {
        for (cy_future_t* const sub : row) {
            if (sub != nullptr) {
                cy_future_destroy(sub);
            }
        }
    }
    e2e::drive_for_all(net, now, 80'000, step_us, false);
    for (const auto& row : pubs) {
        for (cy_publisher_t* const pub : row) {
            cy_unadvertise(pub);
        }
    }
    e2e::drive_for_all(net, now, 80'000, step_us, false);

    e2e::drain_queue_all(net, now, step_us, 80'000U);
    e2e::assert_quiescent(net);
    e2e::sim_net_deinit(net);
    e2e::assert_all_node_heaps_clean(net);
}

void test_api_consensus_e2e_m06_node_restart_rejoin_during_collision_migration()
{
    constexpr std::size_t node_count   = 5U;
    constexpr std::size_t restart_node = 4U;
    constexpr std::size_t topic_count  = 2U;

    e2e::sim_net_config_t cfg{};
    cfg.node_count       = node_count;
    cfg.random_seed_base = UINT64_C(0xA060);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    std::vector<arrival_capture_t>            captures(node_count);
    std::vector<std::vector<cy_future_t*>>    subs(node_count, std::vector<cy_future_t*>(topic_count, nullptr));
    std::vector<std::vector<cy_publisher_t*>> pubs(node_count, std::vector<cy_publisher_t*>(topic_count, nullptr));
    std::vector<std::vector<std::uint64_t>>   seq(node_count, std::vector<std::uint64_t>(topic_count, 0U));

    const auto create_node_handles = [&](const std::size_t node) {
        for (std::size_t topic = 0U; topic < topic_count; topic++) {
            if (subs.at(node).at(topic) == nullptr) {
                subs.at(node).at(topic) =
                  cy_subscribe(e2e::sim_net_cy(net, node), cy_str(colliding_topics.at(topic)), 64U);
                TEST_ASSERT_NOT_NULL(subs.at(node).at(topic));
                cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
                ctx.ptr[0]            = &captures.at(node);
                cy_future_context_set(subs.at(node).at(topic), ctx);
                cy_future_callback_set(subs.at(node).at(topic), on_arrival_capture);
            }
            if (pubs.at(node).at(topic) == nullptr) {
                pubs.at(node).at(topic) = cy_advertise(e2e::sim_net_cy(net, node), cy_str(colliding_topics.at(topic)));
                TEST_ASSERT_NOT_NULL(pubs.at(node).at(topic));
            }
        }
    };

    for (std::size_t node = 0U; node < node_count; node++) {
        create_node_handles(node);
    }

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, 600'000, step_us, false);

    for (std::size_t round = 0U; round < 32U; round++) {
        if (round == 14U) {
            for (std::size_t topic = 0U; topic < topic_count; topic++) {
                if (subs.at(restart_node).at(topic) != nullptr) {
                    cy_future_destroy(subs.at(restart_node).at(topic));
                    subs.at(restart_node).at(topic) = nullptr;
                }
                if (pubs.at(restart_node).at(topic) != nullptr) {
                    cy_unadvertise(pubs.at(restart_node).at(topic));
                    pubs.at(restart_node).at(topic) = nullptr;
                }
            }
            e2e::drive_for_all(net, now, 140'000, step_us, false);
            create_node_handles(restart_node);
            e2e::drive_for_all(net, now, 180'000, step_us, false);
        }

        e2e::set_now_all(net, now);
        for (std::size_t node = 0U; node < node_count; node++) {
            for (std::size_t topic = 0U; topic < topic_count; topic++) {
                if (pubs.at(node).at(topic) == nullptr) {
                    continue;
                }
                const cy_err_t err = publish_best_effort(
                  pubs.at(node).at(topic), pub_id_for_topic(node, topic), ++seq.at(node).at(topic), now);
                TEST_ASSERT_EQUAL_INT(CY_OK, err);
            }
        }
        e2e::drive_for_all(net, now, 20'000, step_us, false);
    }
    e2e::drive_for_all(net, now, 280'000, step_us, false);

    for (const arrival_capture_t& capture : captures) {
        TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    }
    for (std::size_t topic = 0U; topic < topic_count; topic++) {
        if (count_by_publisher(captures.at(restart_node), pub_id_for_topic(0U, topic)) == 0U) {
            const std::string msg = "m06 restart receiver missing topic_index=" + std::to_string(topic) +
                                    " pub_id=" + std::to_string(pub_id_for_topic(0U, topic));
            TEST_FAIL_MESSAGE(msg.c_str());
        }
    }
    for (std::size_t topic = 0U; topic < topic_count; topic++) {
        std::size_t receivers = 0U;
        for (std::size_t receiver = 0U; receiver < node_count; receiver++) {
            if (receiver == restart_node) {
                continue;
            }
            if (count_by_publisher(captures.at(receiver), pub_id_for_topic(restart_node, topic)) > 0U) {
                receivers++;
            }
        }
        if (receivers == 0U) {
            const std::string msg = "m06 restart sender missing topic_index=" + std::to_string(topic) +
                                    " pub_id=" + std::to_string(pub_id_for_topic(restart_node, topic));
            TEST_FAIL_MESSAGE(msg.c_str());
        }
    }

    e2e::sim_net_faults_set(net, nullptr, nullptr);
    for (const auto& row : subs) {
        for (cy_future_t* const sub : row) {
            if (sub != nullptr) {
                cy_future_destroy(sub);
            }
        }
    }
    e2e::drive_for_all(net, now, 80'000, step_us, false);
    for (const auto& row : pubs) {
        for (cy_publisher_t* const pub : row) {
            if (pub != nullptr) {
                cy_unadvertise(pub);
            }
        }
    }
    e2e::drive_for_all(net, now, 80'000, step_us, false);

    e2e::drain_queue_all(net, now, step_us, 80'000U);
    e2e::assert_quiescent(net);
    e2e::sim_net_deinit(net);
    e2e::assert_all_node_heaps_clean(net);
}

void test_api_consensus_e2e_m07_spin_failures_with_gossip_churn_eventual_recovery()
{
    std::size_t          spin_failures = 35U;
    e2e::fault_plan_t    frame_faults{};
    e2e::op_fault_plan_t op_faults{};
    e2e::fault_plan_add_delay(
      frame_faults,
      12'000,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(7U), e2e::fault_predicate_every_nth(2U) }));
    e2e::fault_plan_add_duplicate(
      frame_faults,
      1U,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(7U), e2e::fault_predicate_every_nth(5U) }));
    e2e::fault_plan_add_drop(
      frame_faults,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(0U), e2e::fault_predicate_every_nth(11U) }));

    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, [&](const e2e::op_info_t& op) {
        if ((op.kind != e2e::op_kind_t::spin) || (op.node_index != 2U)) {
            return false;
        }
        if (spin_failures == 0U) {
            return false;
        }
        spin_failures--;
        return true;
    });

    one_topic_env_t env{};
    one_topic_init(env, 5U, UINT64_C(0xA070), "e2e/multi/m07/topic", &frame_faults, &op_faults);
    cy_us_t now = 0;

    for (std::size_t round = 0U; round < 48U; round++) {
        e2e::set_now_all(env.net, now);
        one_topic_publish_round(env, now);
        e2e::drive_for_all(env.net, now, 20'000, step_us, true);
    }
    e2e::drive_for_all(env.net, now, 300'000, step_us, true);

    one_topic_assert_reachability(env);
    TEST_ASSERT_TRUE(
      std::ranges::any_of(e2e::sim_net_op_fault_captures(env.net), [](const e2e::op_fault_capture_t& capture) {
          return capture.failed && (capture.op.kind == e2e::op_kind_t::spin);
      }));

    one_topic_cleanup(env, now);
}

void test_api_consensus_e2e_m08_mixed_faults_and_platform_failures_stress()
{
    e2e::fault_plan_t    frame_faults{};
    e2e::op_fault_plan_t op_faults{};

    e2e::fault_plan_add_delay(
      frame_faults,
      8'000,
      e2e::fault_predicate_all_of(
        { e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(0U), e2e::fault_predicate_header_type(7U) }),
          e2e::fault_predicate_every_nth(3U) }));
    e2e::fault_plan_add_drop(
      frame_faults,
      e2e::fault_predicate_all_of(
        { e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(0U), e2e::fault_predicate_header_type(7U) }),
          e2e::fault_predicate_every_nth(13U) }));

    e2e::op_fault_plan_add_fail(
      op_faults,
      CY_ERR_MEDIA,
      e2e::op_fault_predicate_all_of({ e2e::op_fault_predicate_kind(e2e::op_kind_t::subject_send),
                                       e2e::op_fault_predicate_node(0U),
                                       e2e::op_fault_predicate_every_nth(3U) }));
    e2e::op_fault_plan_add_fail(op_faults,
                                CY_ERR_MEDIA,
                                e2e::op_fault_predicate_all_of({ e2e::op_fault_predicate_kind(e2e::op_kind_t::spin),
                                                                 e2e::op_fault_predicate_node(1U),
                                                                 e2e::op_fault_predicate_every_nth(5U) }));

    one_topic_env_t env{};
    one_topic_init(env, 5U, UINT64_C(0xA080), "e2e/multi/m08/topic", &frame_faults, &op_faults);
    cy_us_t now = 0;

    for (std::size_t round = 0U; round < 64U; round++) {
        e2e::set_now_all(env.net, now);
        one_topic_publish_round(env, now);
        e2e::drive_for_all(env.net, now, 20'000, step_us, true);
    }
    e2e::drive_for_all(env.net, now, 350'000, step_us, true);

    one_topic_assert_reachability(env);
    one_topic_cleanup(env, now);
}

void test_api_consensus_e2e_m09_stale_gossip_replay_does_not_shift_stable_mapping()
{
    constexpr std::size_t node_count  = 5U;
    constexpr std::size_t topic_count = 2U;

    e2e::sim_net_config_t cfg{};
    cfg.node_count       = node_count;
    cfg.random_seed_base = UINT64_C(0xA090);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    std::vector<cy_publisher_t*> pubs{};
    pubs.reserve(node_count * topic_count);
    std::vector<std::vector<cy_publisher_t*>> by_node(node_count, std::vector<cy_publisher_t*>(topic_count, nullptr));
    std::vector<std::vector<cy_future_t*>>    subs(node_count, std::vector<cy_future_t*>(topic_count, nullptr));
    std::vector<arrival_capture_t>            captures(node_count);
    std::vector<std::vector<std::uint64_t>>   seq(node_count, std::vector<std::uint64_t>(topic_count, 0U));

    for (std::size_t node = 0U; node < node_count; node++) {
        for (std::size_t topic = 0U; topic < topic_count; topic++) {
            subs.at(node).at(topic) = cy_subscribe(e2e::sim_net_cy(net, node), cy_str(colliding_topics.at(topic)), 64U);
            TEST_ASSERT_NOT_NULL(subs.at(node).at(topic));
            cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
            ctx.ptr[0]            = &captures.at(node);
            cy_future_context_set(subs.at(node).at(topic), ctx);
            cy_future_callback_set(subs.at(node).at(topic), on_arrival_capture);

            by_node.at(node).at(topic) = cy_advertise(e2e::sim_net_cy(net, node), cy_str(colliding_topics.at(topic)));
            TEST_ASSERT_NOT_NULL(by_node.at(node).at(topic));
            pubs.push_back(by_node.at(node).at(topic));
        }
    }

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, 800'000, step_us, false);

    std::array<std::uint64_t, topic_count> hashes{};
    for (std::size_t topic = 0U; topic < topic_count; topic++) {
        const cy_topic_t* const t = cy_topic_find_by_name(e2e::sim_net_cy(net, 0U), cy_str(colliding_topics.at(topic)));
        TEST_ASSERT_NOT_NULL(t);
        hashes.at(topic) = cy_topic_hash(t);
    }

    for (std::size_t round = 0U; round < 24U; round++) {
        e2e::set_now_all(net, now);
        for (std::size_t node = 0U; node < node_count; node++) {
            for (std::size_t topic = 0U; topic < topic_count; topic++) {
                const cy_err_t err = publish_best_effort(
                  by_node.at(node).at(topic), pub_id_for_topic(node, topic), ++seq.at(node).at(topic), now);
                TEST_ASSERT_EQUAL_INT(CY_OK, err);
            }
        }
        e2e::drive_for_all(net, now, 20'000, step_us, false);
    }
    e2e::drive_for_all(net, now, 260'000, step_us, false);

    std::array<std::uint32_t, topic_count> stable_subjects{};
    for (std::size_t topic = 0U; topic < topic_count; topic++) {
        const auto subject = last_subject_for_hash_any(e2e::sim_net_captures(net), hashes.at(topic));
        if (!subject.has_value()) {
            const std::string msg =
              "m09 missing stable subject topic_index=" + std::to_string(topic) +
              " topic_hash=" + std::to_string(hashes.at(topic)) +
              " pub_frames=" + std::to_string(count_pub_frames_for_hash(e2e::sim_net_captures(net), hashes.at(topic)));
            TEST_FAIL_MESSAGE(msg.c_str());
        }
        stable_subjects.at(topic) = *subject;
    }

    for (std::size_t node = 0U; node < node_count; node++) {
        for (std::size_t topic = 0U; topic < topic_count; topic++) {
            inject_divergent_gossip(net,
                                    node,
                                    UINT64_C(0xAA000000) + (static_cast<std::uint64_t>(topic) * 32U) + node,
                                    hashes.at(topic),
                                    0U,
                                    colliding_topics.at(topic),
                                    now);
        }
    }
    e2e::drive_for_all(net, now, 420'000, step_us, false);

    for (std::size_t round = 0U; round < 10U; round++) {
        e2e::set_now_all(net, now);
        for (std::size_t node = 0U; node < node_count; node++) {
            for (std::size_t topic = 0U; topic < topic_count; topic++) {
                const cy_err_t err = publish_best_effort(
                  by_node.at(node).at(topic), pub_id_for_topic(node, topic), ++seq.at(node).at(topic), now);
                TEST_ASSERT_EQUAL_INT(CY_OK, err);
            }
        }
        e2e::drive_for_all(net, now, 20'000, step_us, false);
    }
    e2e::drive_for_all(net, now, 260'000, step_us, false);

    for (std::size_t topic = 0U; topic < topic_count; topic++) {
        for (std::size_t node = 0U; node < node_count; node++) {
            const auto subject = last_subject_for_hash(e2e::sim_net_captures(net), node, hashes.at(topic));
            if (!subject.has_value()) {
                const std::string msg = "m09 missing per-node subject node=" + std::to_string(node) +
                                        " topic_index=" + std::to_string(topic) +
                                        " topic_hash=" + std::to_string(hashes.at(topic));
                TEST_FAIL_MESSAGE(msg.c_str());
            }
            TEST_ASSERT_EQUAL_UINT32(stable_subjects.at(topic), *subject);
        }
    }

    e2e::sim_net_faults_set(net, nullptr, nullptr);
    for (const auto& row : subs) {
        for (cy_future_t* const sub : row) {
            if (sub != nullptr) {
                cy_future_destroy(sub);
            }
        }
    }
    e2e::drive_for_all(net, now, 80'000, step_us, false);
    for (cy_publisher_t* const pub : pubs) {
        cy_unadvertise(pub);
    }
    e2e::drive_for_all(net, now, 80'000, step_us, false);

    e2e::drain_queue_all(net, now, step_us, 80'000U);
    e2e::assert_quiescent(net);
    e2e::sim_net_deinit(net);
    e2e::assert_all_node_heaps_clean(net);
}

std::vector<std::uint64_t> deterministic_transcript_run(const std::uint64_t seed)
{
    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(
      faults,
      7'000,
      e2e::fault_predicate_all_of(
        { e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(0U), e2e::fault_predicate_header_type(7U) }),
          e2e::fault_predicate_every_nth(2U) }));
    e2e::fault_plan_add_drop(
      faults,
      e2e::fault_predicate_all_of(
        { e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(0U), e2e::fault_predicate_header_type(7U) }),
          e2e::fault_predicate_every_nth(11U) }));

    one_topic_env_t env{};
    one_topic_init(env, 5U, seed, "e2e/multi/m10/topic", &faults);
    cy_us_t now = 0;

    for (std::size_t round = 0U; round < 40U; round++) {
        e2e::set_now_all(env.net, now);
        one_topic_publish_round(env, now);
        e2e::drive_for_all(env.net, now, 20'000, step_us, false);
    }
    e2e::drive_for_all(env.net, now, 250'000, step_us, false);

    std::vector<std::uint64_t> transcript{};
    transcript.reserve(e2e::sim_net_captures(env.net).size() + 4U);
    std::transform(e2e::sim_net_captures(env.net).begin(),
                   e2e::sim_net_captures(env.net).end(),
                   std::back_inserter(transcript),
                   [](const e2e::frame_capture_t& cap) { return capture_fingerprint(cap); });
    std::uint64_t summary = UINT64_C(0x123456789ABCDEF0);
    for (const arrival_capture_t& capture : env.captures) {
        summary = mix_hash(summary, capture.samples.size());
        summary = mix_hash(summary, capture.malformed);
    }
    transcript.push_back(summary);

    one_topic_cleanup(env, now);
    return transcript;
}

void test_api_consensus_e2e_m10_deterministic_seed_replay_identical_transcript()
{
    const std::vector<std::uint64_t> run_a = deterministic_transcript_run(UINT64_C(0xA100));
    const std::vector<std::uint64_t> run_b = deterministic_transcript_run(UINT64_C(0xA100));

    TEST_ASSERT_EQUAL_size_t(run_a.size(), run_b.size());
    for (std::size_t i = 0U; i < run_a.size(); i++) {
        TEST_ASSERT_EQUAL_UINT64(run_a.at(i), run_b.at(i));
    }
}

void test_colliding_topics_selftest()
{
    constexpr auto modulus = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit);
    const auto     sid_0   = rapidhash(colliding_topics.at(0), strlen(colliding_topics.at(0))) % modulus;
    for (std::size_t i = 1U; i < colliding_topics.size(); i++) {
        TEST_ASSERT_EQUAL_UINT64(sid_0, rapidhash(colliding_topics.at(i), strlen(colliding_topics.at(i))) % modulus);
    }
}

} // namespace

extern "C" void setUp()
{
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
    cy_test_message_reset_counters();
}

extern "C" void tearDown() { TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count()); }

int main()
{
    UNITY_BEGIN();
    RUN_TEST(test_colliding_topics_selftest);
    RUN_TEST(test_api_consensus_e2e_m01_five_node_baseline_convergence);
    RUN_TEST(test_api_consensus_e2e_m02_split_partition_heal_eventual_delivery);
    RUN_TEST(test_api_consensus_e2e_m03_bridge_node_isolation_then_restore);
    RUN_TEST(test_api_consensus_e2e_m04_rotating_partitions_eventual_recovery);
    RUN_TEST(test_api_consensus_e2e_m05_three_colliding_topics_subject_uniqueness);
    RUN_TEST(test_api_consensus_e2e_m06_node_restart_rejoin_during_collision_migration);
    RUN_TEST(test_api_consensus_e2e_m07_spin_failures_with_gossip_churn_eventual_recovery);
    RUN_TEST(test_api_consensus_e2e_m08_mixed_faults_and_platform_failures_stress);
    RUN_TEST(test_api_consensus_e2e_m09_stale_gossip_replay_does_not_shift_stable_mapping);
    RUN_TEST(test_api_consensus_e2e_m10_deterministic_seed_replay_identical_transcript);
    return UNITY_END();
}
