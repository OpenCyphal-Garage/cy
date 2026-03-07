#include <cy_platform.h>
#include <unity.h>
#include "e2e_faults.hpp"
#include "e2e_sim_net.hpp"
#include "e2e_test_utils.hpp"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <set>
#include <tuple>
#include <vector>

namespace {
constexpr std::uint8_t header_msg_rel = 1U;
constexpr std::uint8_t header_msg_ack = 2U;

constexpr std::size_t topic_count   = 2U;
constexpr std::size_t max_pub_slots = 64U;

constexpr cy_us_t step_us        = 20'000;
constexpr cy_us_t future_timeout = 3'000'000;

constexpr std::array<const char*, topic_count> colliding_topics = {
    "e2e/migrate/topic_alpha#123456789abcdeff",
    "e2e/migrate/topic_beta#123456789abebef2",
};

struct global_stats_t final
{
    std::size_t scenarios{ 0U };
    std::size_t async_errors{ 0U };
} g_stats; // NOLINT(cppcoreguidelines-avoid-non-const-global-variables)

struct subscriber_log_t final
{
    std::set<std::tuple<std::size_t, std::size_t, std::uint32_t, std::uint64_t>>                       unique{};
    std::array<std::array<std::array<std::uint64_t, max_pub_slots>, topic_count>, e2e::sim_node_count> last_seq{};
    std::array<std::array<std::array<bool, max_pub_slots>, topic_count>, e2e::sim_node_count>          has_last{};
    std::array<std::array<std::array<std::size_t, max_pub_slots>, topic_count>, e2e::sim_node_count>   count{};
    std::size_t malformed_count{ 0U };
    std::size_t duplicate_count{ 0U };
};

struct subscriber_context_t final
{
    subscriber_log_t* log{ nullptr };
    std::size_t       receiver_node{ 0U };
    std::size_t       topic_index{ 0U };
    bool              ordered{ false };
};

struct handles_t final
{
    std::array<std::array<cy_publisher_t*, topic_count>, e2e::sim_node_count>      pub{};
    std::array<std::array<cy_future_t*, topic_count>, e2e::sim_node_count>         sub{};
    std::array<std::array<subscriber_context_t, topic_count>, e2e::sim_node_count> ctx{};
    std::array<std::array<std::uint64_t, topic_count>, e2e::sim_node_count>        next_seq{};
};

struct future_state_t final
{
    cy_future_t* future{ nullptr };
    std::size_t  topic_index{ 0U };
    cy_us_t      deadline{ 0 };
};

struct e_case_config_t final
{
    bool ordered_receiver{ false };
    bool drop_data{ false };
    bool drop_ack{ false };
    bool reorder{ false };
    bool multi_future{ false };
    bool destroy_publisher_midstream{ false };
    bool destroy_subscriber_midstream{ false };

    bool require_all_futures_success{ true };
    bool require_receiver_samples{ true };

    std::size_t rounds{ 10U };
    std::size_t concurrent{ 1U };

    std::uint64_t seed{ 1U };
};

struct e_case_result_t final
{
    std::size_t success_futures{ 0U };
    std::size_t failed_futures{ 0U };
    std::size_t pending_futures{ 0U };

    std::array<std::uint64_t, topic_count> topic_hashes{};
    std::array<std::uint32_t, topic_count> preferred_subjects{};

    subscriber_log_t           log{};
    std::vector<std::uint64_t> transcript{};
};

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

std::uint32_t pub_id_for(const std::size_t node_index, const std::size_t topic_index)
{
    return static_cast<std::uint32_t>((node_index * 16U) + topic_index);
}

std::uint32_t preferred_subject_id(const cy_platform_t* const platform, const std::uint64_t topic_hash)
{
    TEST_ASSERT_NOT_NULL(platform);
    TEST_ASSERT_TRUE(topic_hash > CY_SUBJECT_ID_PINNED_MAX);
    return static_cast<std::uint32_t>(CY_SUBJECT_ID_PINNED_MAX + 1U + (topic_hash % platform->subject_id_modulus));
}

std::uint64_t topic_hash_for(const cy_t* const cy, const char* const topic_name)
{
    const cy_topic_t* const topic = cy_topic_find_by_name(cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(topic);
    return cy_topic_hash(topic);
}

void drive_for(e2e::sim_net_t& net, cy_us_t& now, const cy_us_t duration)
{
    const cy_us_t end = now + duration;
    while (now < end) {
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }
}

void drain_queue(e2e::sim_net_t& net, cy_us_t& now)
{
    std::size_t guard = 0U;
    while (e2e::sim_net_pending_frames(net) > 0U) {
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
        guard++;
        TEST_ASSERT_TRUE(guard < 20'000U);
    }
}

void destroy_futures(std::vector<future_state_t>& futures)
{
    for (future_state_t& f : futures) {
        if (f.future != nullptr) {
            cy_future_destroy(f.future);
            f.future = nullptr;
        }
    }
}

void destroy_futures_for_topic(std::vector<future_state_t>& futures, const std::size_t topic_index)
{
    for (future_state_t& f : futures) {
        if ((f.future != nullptr) && (f.topic_index == topic_index)) {
            cy_future_destroy(f.future);
            f.future = nullptr;
        }
    }
}

void compact_futures(std::vector<future_state_t>& futures)
{
    std::erase_if(futures, [](const future_state_t& f) { return f.future == nullptr; });
}

void destroy_all_handles(e2e::sim_net_t& net, handles_t& handles, cy_us_t& now)
{
    for (std::size_t node = 0U; node < e2e::sim_node_count; node++) {
        for (std::size_t t = 0U; t < topic_count; t++) {
            if (handles.sub.at(node).at(t) != nullptr) {
                cy_future_destroy(handles.sub.at(node).at(t));
                handles.sub.at(node).at(t) = nullptr;
            }
        }
    }
    drive_for(net, now, 80'000);

    for (std::size_t node = 0U; node < e2e::sim_node_count; node++) {
        for (std::size_t t = 0U; t < topic_count; t++) {
            if (handles.pub.at(node).at(t) != nullptr) {
                cy_unadvertise(handles.pub.at(node).at(t));
                handles.pub.at(node).at(t) = nullptr;
            }
        }
    }
    drive_for(net, now, 80'000);
}

extern "C" void on_arrival_capture(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }

    auto* const ctx = static_cast<subscriber_context_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(ctx);
    TEST_ASSERT_NOT_NULL(ctx->log);

    std::array<unsigned char, 16> bytes{};
    const std::size_t             size = cy_message_read(arrival.message.content, 0U, bytes.size(), bytes.data());

    e2e::app_payload_t payload{};
    if (!e2e::app_payload_unpack(bytes.data(), size, payload)) {
        ctx->log->malformed_count++;
        cy_message_refcount_dec(arrival.message.content);
        return;
    }

    const std::size_t slot = payload.publisher_id % max_pub_slots;
    if (ctx->ordered && ctx->log->has_last.at(ctx->receiver_node).at(ctx->topic_index).at(slot)) {
        TEST_ASSERT_TRUE(payload.sequence > ctx->log->last_seq.at(ctx->receiver_node).at(ctx->topic_index).at(slot));
    }
    ctx->log->has_last.at(ctx->receiver_node).at(ctx->topic_index).at(slot) = true;
    ctx->log->last_seq.at(ctx->receiver_node).at(ctx->topic_index).at(slot) = payload.sequence;
    ctx->log->count.at(ctx->receiver_node).at(ctx->topic_index).at(slot)++;

    const auto key = std::make_tuple(ctx->receiver_node, ctx->topic_index, payload.publisher_id, payload.sequence);
    if (!ctx->log->unique.insert(key).second) {
        ctx->log->duplicate_count++;
    }
    cy_message_refcount_dec(arrival.message.content);
}

void create_topic_handles(e2e::sim_net_t&   net,
                          handles_t&        handles,
                          subscriber_log_t& log,
                          const std::size_t node_index,
                          const std::size_t topic_index,
                          const bool        ordered_receiver)
{
    const bool ordered = (node_index == e2e::sim_node_b) ? ordered_receiver : false;

    cy_publisher_t* const pub =
      cy_advertise(e2e::sim_net_cy(net, node_index), cy_str(colliding_topics.at(topic_index)));
    TEST_ASSERT_NOT_NULL(pub);
    cy_ack_timeout_set(pub, 60'000);
    handles.pub.at(node_index).at(topic_index) = pub;

    cy_future_t* sub = nullptr;
    if (ordered) {
        sub = cy_subscribe_ordered(
          e2e::sim_net_cy(net, node_index), cy_str(colliding_topics.at(topic_index)), 1024U, 60'000);
    } else {
        sub = cy_subscribe(e2e::sim_net_cy(net, node_index), cy_str(colliding_topics.at(topic_index)), 1024U);
    }
    TEST_ASSERT_NOT_NULL(sub);
    handles.sub.at(node_index).at(topic_index) = sub;

    subscriber_context_t& ctx = handles.ctx.at(node_index).at(topic_index);
    ctx.log                   = &log;
    ctx.receiver_node         = node_index;
    ctx.topic_index           = topic_index;
    ctx.ordered               = ordered;

    cy_user_context_t user_ctx = CY_USER_CONTEXT_EMPTY;
    user_ctx.ptr[0]            = &ctx;
    cy_future_context_set(sub, user_ctx);
    cy_future_callback_set(sub, on_arrival_capture);
}

std::optional<std::uint64_t> publish_best_effort(handles_t&        handles,
                                                 const std::size_t node_index,
                                                 const std::size_t topic_index,
                                                 const cy_us_t     now)
{
    cy_publisher_t* const pub = handles.pub.at(node_index).at(topic_index);
    if (pub == nullptr) {
        return std::nullopt;
    }

    const std::uint32_t pub_id  = pub_id_for(node_index, topic_index);
    const std::uint64_t seq     = ++handles.next_seq.at(node_index).at(topic_index);
    const auto          payload = e2e::app_payload_pack(pub_id, seq);
    const cy_bytes_t    msg     = { payload.size(), payload.data(), nullptr };
    if (cy_publish(pub, now + 200'000, msg) != CY_OK) {
        return std::nullopt;
    }
    return seq;
}

future_state_t publish_reliable(handles_t&        handles,
                                const std::size_t node_index,
                                const std::size_t topic_index,
                                const cy_us_t     now)
{
    future_state_t out{};

    cy_publisher_t* const pub = handles.pub.at(node_index).at(topic_index);
    TEST_ASSERT_NOT_NULL(pub);

    const std::uint32_t pub_id  = pub_id_for(node_index, topic_index);
    const std::uint64_t seq     = ++handles.next_seq.at(node_index).at(topic_index);
    const auto          payload = e2e::app_payload_pack(pub_id, seq);
    const cy_bytes_t    msg     = { payload.size(), payload.data(), nullptr };

    out.topic_index = topic_index;
    out.deadline    = now + future_timeout;
    out.future      = cy_publish_reliable(pub, out.deadline, msg);
    TEST_ASSERT_NOT_NULL(out.future);
    return out;
}

e2e::fault_plan_t build_fault_plan(const e_case_config_t& cfg)
{
    e2e::fault_plan_t plan{};
    const auto        in_window = e2e::fault_predicate_send_time(120'000, 900'000);
    const auto        rel       = e2e::fault_predicate_header_type(header_msg_rel);
    const auto        ack       = e2e::fault_predicate_header_type(header_msg_ack);

    if (cfg.drop_data) {
        e2e::fault_plan_add_drop(plan,
                                 e2e::fault_predicate_all_of({ rel, in_window, e2e::fault_predicate_every_nth(4U) }));
    }
    if (cfg.drop_ack) {
        e2e::fault_plan_add_drop(plan,
                                 e2e::fault_predicate_all_of({ ack, in_window, e2e::fault_predicate_every_nth(3U) }));
    }
    if (cfg.reorder) {
        e2e::fault_plan_add_delay(plan, 18'000, e2e::fault_predicate_all_of({ rel, in_window }));
    }
    if (cfg.drop_data && cfg.drop_ack && cfg.reorder) {
        e2e::fault_plan_add_duplicate(
          plan, 1U, e2e::fault_predicate_all_of({ rel, in_window, e2e::fault_predicate_every_nth(5U) }));
    }
    return plan;
}

void summarize_futures(const std::vector<future_state_t>& futures,
                       std::size_t&                       success,
                       std::size_t&                       failure,
                       std::size_t&                       pending)
{
    success = 0U;
    failure = 0U;
    pending = 0U;
    for (const future_state_t& item : futures) {
        if (item.future == nullptr) {
            continue;
        }
        if (!cy_future_done(item.future)) {
            pending++;
        } else if (cy_future_error(item.future) == CY_OK) {
            success++;
        } else {
            failure++;
        }
    }
}

void wait_futures(e2e::sim_net_t&                    net,
                  cy_us_t&                           now,
                  const std::vector<future_state_t>& futures,
                  std::size_t&                       success,
                  std::size_t&                       failure,
                  std::size_t&                       pending)
{
    cy_us_t max_deadline = now;
    for (const future_state_t& item : futures) {
        if (item.future == nullptr) {
            continue;
        }
        max_deadline = std::max(max_deadline, item.deadline);
    }

    for (std::size_t i = 0U; i < 800U; i++) {
        summarize_futures(futures, success, failure, pending);
        if ((pending == 0U) || (now > (max_deadline + 2'000'000))) {
            return;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }
}

void build_transcript(const e2e::sim_net_t& net, e_case_result_t& result)
{
    result.transcript.clear();
    result.transcript.reserve(e2e::sim_net_captures(net).size() + result.log.unique.size() + 8U);

    for (const e2e::frame_capture_t& cap : e2e::sim_net_captures(net)) {
        result.transcript.push_back(capture_fingerprint(cap));
    }

    for (const auto& key : result.log.unique) {
        std::uint64_t h = UINT64_C(0x84222325CBF29CE4);
        h               = mix_hash(h, std::get<0>(key));
        h               = mix_hash(h, std::get<1>(key));
        h               = mix_hash(h, std::get<2>(key));
        h               = mix_hash(h, std::get<3>(key));
        result.transcript.push_back(h);
    }

    std::uint64_t summary = UINT64_C(0x123456789ABCDEF0);
    summary               = mix_hash(summary, result.success_futures);
    summary               = mix_hash(summary, result.failed_futures);
    summary               = mix_hash(summary, result.pending_futures);
    summary               = mix_hash(summary, result.log.malformed_count);
    summary               = mix_hash(summary, result.log.duplicate_count);
    result.transcript.push_back(summary);
}

e_case_result_t run_e_case(const e_case_config_t& cfg)
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), cfg.seed));

    const e2e::fault_plan_t faults = build_fault_plan(cfg);
    if (faults.rules.empty()) {
        e2e::sim_net_faults_set(net, nullptr);
    } else {
        e2e::sim_net_faults_set(net, &faults);
    }

    e_case_result_t result{};
    handles_t       handles{};
    cy_us_t         now = 0;

    for (std::size_t t = 0U; t < topic_count; t++) {
        for (std::size_t node = 0U; node < e2e::sim_node_count; node++) {
            create_topic_handles(net, handles, result.log, node, t, cfg.ordered_receiver);
        }
    }

    drive_for(net, now, 120'000);

    for (std::size_t t = 0U; t < topic_count; t++) {
        result.topic_hashes.at(t) = topic_hash_for(e2e::sim_net_cy(net, e2e::sim_node_a), colliding_topics.at(t));
        result.preferred_subjects.at(t) =
          preferred_subject_id(e2e::sim_net_platform(net, e2e::sim_node_a), result.topic_hashes.at(t));
    }
    TEST_ASSERT_EQUAL_UINT32(result.preferred_subjects.at(0U), result.preferred_subjects.at(1U));

    std::vector<future_state_t> futures{};
    bool                        publisher_destroyed  = false;
    bool                        subscriber_destroyed = false;

    const std::size_t concurrent = cfg.multi_future ? cfg.concurrent : 1U;

    for (std::size_t round = 0U; round < cfg.rounds; round++) {
        if (cfg.destroy_publisher_midstream && !publisher_destroyed && (round >= (cfg.rounds / 2U))) {
            if (handles.pub.at(e2e::sim_node_a).at(0U) != nullptr) {
                // Some implementations invalidate publisher-owned futures on unadvertise.
                destroy_futures_for_topic(futures, 0U);
                compact_futures(futures);
                cy_unadvertise(handles.pub.at(e2e::sim_node_a).at(0U));
                handles.pub.at(e2e::sim_node_a).at(0U) = nullptr;
            }
            publisher_destroyed = true;
        }

        if (cfg.destroy_subscriber_midstream && !subscriber_destroyed && (round >= (cfg.rounds / 2U))) {
            if (handles.sub.at(e2e::sim_node_b).at(0U) != nullptr) {
                cy_future_destroy(handles.sub.at(e2e::sim_node_b).at(0U));
                handles.sub.at(e2e::sim_node_b).at(0U) = nullptr;
            }
            subscriber_destroyed = true;
            drive_for(net, now, 80'000);
        }

        for (std::size_t t = 0U; t < topic_count; t++) {
            if (handles.pub.at(e2e::sim_node_a).at(t) != nullptr) {
                for (std::size_t i = 0U; i < concurrent; i++) {
                    futures.push_back(publish_reliable(handles, e2e::sim_node_a, t, now));
                }
            }
            (void)publish_best_effort(handles, e2e::sim_node_b, t, now);
        }

        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }

    drive_for(net, now, 2'000'000);
    wait_futures(net, now, futures, result.success_futures, result.failed_futures, result.pending_futures);
    TEST_ASSERT_EQUAL_size_t(0U, result.pending_futures);

    if (cfg.require_all_futures_success) {
        TEST_ASSERT_TRUE(result.success_futures > 0U);
        TEST_ASSERT_EQUAL_size_t(0U, result.failed_futures);
    }

    TEST_ASSERT_EQUAL_size_t(0U, result.log.malformed_count);
    TEST_ASSERT_EQUAL_size_t(0U, result.log.duplicate_count);

    if (cfg.require_receiver_samples) {
        for (std::size_t t = 0U; t < topic_count; t++) {
            const std::size_t slot = pub_id_for(e2e::sim_node_a, t) % max_pub_slots;
            TEST_ASSERT_TRUE(result.log.count.at(e2e::sim_node_b).at(t).at(slot) > 0U);
        }
    }

    build_transcript(net, result);

    destroy_futures(futures);
    destroy_all_handles(net, handles, now);

    drain_queue(net, now);
    e2e::assert_quiescent(net);

    g_stats.scenarios++;
    g_stats.async_errors += e2e::sim_net_async_errors(net).size();

    e2e::sim_net_deinit(net);
    e2e::assert_all_heaps_clean(net);
    e2e::assert_no_live_messages();

    return result;
}

e_case_config_t base_cfg()
{
    e_case_config_t cfg{};
    cfg.rounds     = 10U;
    cfg.concurrent = 1U;
    return cfg;
}

void test_api_pubsub_e2e_e01_publisher_destroyed_with_pending_futures_under_fault_load()
{
    e_case_config_t cfg             = base_cfg();
    cfg.drop_data                   = true;
    cfg.drop_ack                    = true;
    cfg.reorder                     = true;
    cfg.multi_future                = true;
    cfg.concurrent                  = 6U;
    cfg.destroy_publisher_midstream = true;
    cfg.require_all_futures_success = false;
    cfg.require_receiver_samples    = false;
    cfg.seed                        = 0xE01U;

    const e_case_result_t res = run_e_case(cfg);
    TEST_ASSERT_TRUE((res.success_futures + res.failed_futures) > 0U);
}

void test_api_pubsub_e2e_e02_subscriber_destroyed_during_retransmission_storm()
{
    e_case_config_t cfg              = base_cfg();
    cfg.drop_data                    = true;
    cfg.drop_ack                     = true;
    cfg.reorder                      = true;
    cfg.multi_future                 = true;
    cfg.concurrent                   = 5U;
    cfg.destroy_subscriber_midstream = true;
    cfg.require_all_futures_success  = false;
    cfg.require_receiver_samples     = false;
    cfg.seed                         = 0xE02U;

    const e_case_result_t res = run_e_case(cfg);
    TEST_ASSERT_TRUE((res.success_futures + res.failed_futures) > 0U);
}

void test_api_pubsub_e2e_e03_determinism_identical_seed_identical_transcript()
{
    e_case_config_t cfg             = base_cfg();
    cfg.drop_data                   = true;
    cfg.drop_ack                    = true;
    cfg.reorder                     = true;
    cfg.multi_future                = true;
    cfg.concurrent                  = 4U;
    cfg.require_all_futures_success = false;
    cfg.require_receiver_samples    = false;
    cfg.seed                        = 0xE03U;

    const e_case_result_t run_a = run_e_case(cfg);
    const e_case_result_t run_b = run_e_case(cfg);

    TEST_ASSERT_EQUAL_size_t(run_a.transcript.size(), run_b.transcript.size());
    TEST_ASSERT_EQUAL_size_t(run_a.success_futures, run_b.success_futures);
    TEST_ASSERT_EQUAL_size_t(run_a.failed_futures, run_b.failed_futures);
    for (std::size_t i = 0U; i < run_a.transcript.size(); i++) {
        TEST_ASSERT_EQUAL_UINT64(run_a.transcript.at(i), run_b.transcript.at(i));
    }
}

void test_api_pubsub_e2e_e04_seed_sweep_stress_with_invariant_assertions()
{
    for (std::uint64_t seed = 0xE040U; seed < 0xE050U; seed++) {
        e_case_config_t cfg             = base_cfg();
        cfg.drop_data                   = true;
        cfg.drop_ack                    = (seed & 1U) != 0U;
        cfg.reorder                     = true;
        cfg.multi_future                = true;
        cfg.concurrent                  = 3U;
        cfg.require_all_futures_success = false;
        cfg.require_receiver_samples    = false;
        cfg.ordered_receiver            = (seed & 2U) != 0U;
        cfg.seed                        = seed;

        const e_case_result_t res = run_e_case(cfg);
        TEST_ASSERT_EQUAL_size_t(0U, res.pending_futures);
        TEST_ASSERT_EQUAL_size_t(0U, res.log.malformed_count);
        TEST_ASSERT_EQUAL_size_t(0U, res.log.duplicate_count);
    }
}

void test_api_pubsub_e2e_e05_no_unexpected_async_errors_on_success_path()
{
    e_case_config_t cfg = base_cfg();
    cfg.seed            = 0xE05U;

    const e_case_result_t res = run_e_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, res.failed_futures);
}

void test_api_pubsub_e2e_e06_end_of_test_global_invariant_checks()
{
    TEST_ASSERT_TRUE(g_stats.scenarios >= 5U);
    TEST_ASSERT_EQUAL_size_t(0U, g_stats.async_errors);
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
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
    RUN_TEST(test_api_pubsub_e2e_e01_publisher_destroyed_with_pending_futures_under_fault_load);
    RUN_TEST(test_api_pubsub_e2e_e02_subscriber_destroyed_during_retransmission_storm);
    RUN_TEST(test_api_pubsub_e2e_e03_determinism_identical_seed_identical_transcript);
    RUN_TEST(test_api_pubsub_e2e_e04_seed_sweep_stress_with_invariant_assertions);
    RUN_TEST(test_api_pubsub_e2e_e05_no_unexpected_async_errors_on_success_path);
    RUN_TEST(test_api_pubsub_e2e_e06_end_of_test_global_invariant_checks);
    return UNITY_END();
}
