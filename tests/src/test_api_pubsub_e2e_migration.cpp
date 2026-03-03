#include <cy_platform.h>
#include <unity.h>
#include "e2e_faults.hpp"
#include "e2e_sim_net.hpp"
#include "e2e_test_utils.hpp"
#include "helpers.h"
#include "message.h"
#include <array>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <optional>
#include <numeric>
#include <set>
#include <tuple>
#include <vector>

namespace {
constexpr std::uint8_t header_msg_be  = 0U;
constexpr std::uint8_t header_msg_rel = 1U;
constexpr std::uint8_t header_msg_ack = 2U;

constexpr std::size_t max_topics    = 3U;
constexpr std::size_t max_pub_slots = 64U;

constexpr cy_us_t step_us        = 20'000;
constexpr cy_us_t future_timeout = 3'000'000;

constexpr std::array<const char*, max_topics> colliding_topics = {
    "e2e/migrate/topic_alpha#123456789abcdeff",
    "e2e/migrate/topic_beta#123456789abebef2",
    "e2e/migrate/topic_gamma#123456789ac09ee5",
};

struct subscriber_log_t final
{
    std::set<std::tuple<std::size_t, std::size_t, std::uint32_t, std::uint64_t>>                      unique{};
    std::array<std::array<std::array<std::uint64_t, max_pub_slots>, max_topics>, e2e::sim_node_count> last_seq{};
    std::array<std::array<std::array<bool, max_pub_slots>, max_topics>, e2e::sim_node_count>          has_last{};
    std::array<std::array<std::array<std::size_t, max_pub_slots>, max_topics>, e2e::sim_node_count>   count{};

    std::size_t duplicate_count{ 0U };
    std::size_t malformed_count{ 0U };
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
    std::array<std::array<cy_publisher_t*, max_topics>, e2e::sim_node_count>      pub{};
    std::array<std::array<cy_subscriber_t*, max_topics>, e2e::sim_node_count>     sub{};
    std::array<std::array<subscriber_context_t, max_topics>, e2e::sim_node_count> ctx{};
    std::array<std::array<std::uint64_t, max_topics>, e2e::sim_node_count>        next_seq{};
};

struct future_state_t final
{
    cy_future_t*  future{ nullptr };
    std::uint32_t pub_id{ 0U };
    std::uint64_t seq{ 0U };
    std::size_t   topic_index{ 0U };
    cy_us_t       deadline{ 0 };
};

struct d_case_config_t final
{
    bool ordered_receiver{ false };
    bool collision_while_idle{ false };
    bool require_transition_observed{ true };
    bool drop_data{ false };
    bool drop_ack{ false };
    bool reorder{ false };
    bool gossip_churn{ false };
    bool multi_future{ false };
    bool stale_old_subject_replay{ false };
    bool receiver_restart_rejoin{ false };
    bool allow_future_failures{ false };

    std::size_t topic_count{ 2U };
    std::size_t rounds{ 12U };
    std::size_t concurrent{ 1U };

    std::uint64_t seed{ 1U };
};

struct d_case_result_t final
{
    std::size_t success_futures{ 0U };
    std::size_t failed_futures{ 0U };
    std::size_t pending_futures{ 0U };

    std::array<std::uint64_t, max_topics> topic_hashes{};
    std::array<std::uint32_t, max_topics> preferred_subjects{};
    std::array<std::uint32_t, max_topics> final_subjects{};

    subscriber_log_t log{};
};

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

bool topic_hash_from_pinned_literal(const char* const topic_name, std::uint64_t& out)
{
    if (topic_name == nullptr) {
        return false;
    }
    const char* const marker = std::strrchr(topic_name, '#');
    if ((marker == nullptr) || (marker[1] == '\0')) {
        return false;
    }
    const char* const begin = marker + 1;
    const char* const end   = begin + std::strlen(begin);
    const auto        res   = std::from_chars(begin, end, out, 16);
    return (res.ec == std::errc{}) && (res.ptr == end);
}

bool is_message_frame(const e2e::frame_info_t& frame)
{
    return (frame.header_type == header_msg_be) || (frame.header_type == header_msg_rel);
}

std::optional<std::uint32_t> first_subject_for_hash(const std::vector<e2e::frame_capture_t>& captures,
                                                    const std::size_t                        src_node,
                                                    const std::uint64_t                      topic_hash,
                                                    const std::size_t                        from_index)
{
    for (std::size_t i = from_index; i < captures.size(); i++) {
        const e2e::frame_capture_t& cap = captures.at(i);
        if (cap.frame.source != src_node) {
            continue;
        }
        if (!is_message_frame(cap.frame) || !cap.frame.has_topic_hash) {
            continue;
        }
        if (cap.frame.topic_hash == topic_hash) {
            return cap.frame.subject_id;
        }
    }
    return std::nullopt;
}

std::optional<std::uint32_t> last_subject_for_hash(const std::vector<e2e::frame_capture_t>& captures,
                                                   const std::size_t                        src_node,
                                                   const std::uint64_t                      topic_hash)
{
    for (std::size_t i = captures.size(); i > 0U; i--) {
        const e2e::frame_capture_t& cap = captures.at(i - 1U);
        if (cap.frame.source != src_node) {
            continue;
        }
        if (!is_message_frame(cap.frame) || !cap.frame.has_topic_hash) {
            continue;
        }
        if (cap.frame.topic_hash == topic_hash) {
            return cap.frame.subject_id;
        }
    }
    return std::nullopt;
}

std::size_t distinct_subject_count_for_hash(const std::vector<e2e::frame_capture_t>& captures,
                                            const std::size_t                        src_node,
                                            const std::uint64_t                      topic_hash)
{
    std::set<std::uint32_t> distinct{};
    for (const e2e::frame_capture_t& cap : captures) {
        if ((cap.frame.source == src_node) && is_message_frame(cap.frame) && cap.frame.has_topic_hash &&
            (cap.frame.topic_hash == topic_hash)) {
            distinct.insert(cap.frame.subject_id);
        }
    }
    return distinct.size();
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

void destroy_futures(std::vector<future_state_t>& futures)
{
    for (future_state_t& item : futures) {
        if (item.future != nullptr) {
            cy_future_destroy(item.future);
            item.future = nullptr;
        }
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

void destroy_node_handles(e2e::sim_net_t&   net,
                          handles_t&        handles,
                          const std::size_t node_index,
                          const std::size_t topic_count,
                          cy_us_t&          now)
{
    for (std::size_t t = 0U; t < topic_count; t++) {
        if (handles.sub.at(node_index).at(t) != nullptr) {
            cy_unsubscribe(handles.sub.at(node_index).at(t));
            handles.sub.at(node_index).at(t) = nullptr;
        }
    }
    drive_for(net, now, 80'000);

    for (std::size_t t = 0U; t < topic_count; t++) {
        if (handles.pub.at(node_index).at(t) != nullptr) {
            cy_unadvertise(handles.pub.at(node_index).at(t));
            handles.pub.at(node_index).at(t) = nullptr;
        }
    }
    drive_for(net, now, 80'000);
}

void destroy_all_handles(e2e::sim_net_t& net, handles_t& handles, const std::size_t topic_count, cy_us_t& now)
{
    for (std::size_t node = 0U; node < e2e::sim_node_count; node++) {
        destroy_node_handles(net, handles, node, topic_count, now);
    }
}

extern "C" void on_arrival_capture(cy_subscriber_t* const sub, const cy_arrival_t arrival)
{
    auto* const ctx = static_cast<subscriber_context_t*>(cy_subscriber_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(ctx);
    TEST_ASSERT_NOT_NULL(ctx->log);

    std::array<unsigned char, 16> bytes{};
    const std::size_t             size = cy_message_read(arrival.message.content, 0U, bytes.size(), bytes.data());

    e2e::app_payload_t payload{};
    if (!e2e::app_payload_unpack(bytes.data(), size, payload)) {
        ctx->log->malformed_count++;
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

    cy_subscriber_t* sub = nullptr;
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
    cy_subscriber_context_set(sub, user_ctx);
    cy_subscriber_callback_set(sub, on_arrival_capture);
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

    out.pub_id      = pub_id_for(node_index, topic_index);
    out.seq         = ++handles.next_seq.at(node_index).at(topic_index);
    out.topic_index = topic_index;
    out.deadline    = now + future_timeout;

    const auto       payload = e2e::app_payload_pack(out.pub_id, out.seq);
    const cy_bytes_t msg     = { payload.size(), payload.data(), nullptr };
    out.future               = cy_publish_reliable(pub, out.deadline, msg);
    TEST_ASSERT_NOT_NULL(out.future);
    return out;
}

e2e::fault_plan_t build_fault_plan(const d_case_config_t& cfg)
{
    e2e::fault_plan_t plan{};
    const auto        in_window = e2e::fault_predicate_send_time(200'000, 1'000'000);
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
    lane.p2p.state[0] = static_cast<unsigned char>(remote_id & 0xFFU);

    cy_on_message(e2e::sim_net_platform(net, dst_node), lane, nullptr, mts);
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
        TEST_ASSERT_NOT_NULL(item.future);
        if (!cy_future_done(item.future)) {
            pending++;
        } else if (cy_publish_delivered(item.future)) {
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
    // NOLINTBEGIN(boost-use-ranges)
    const cy_us_t max_deadline =
      std::accumulate(futures.begin(), futures.end(), now, [](const cy_us_t acc, const future_state_t& item) {
          return std::max(acc, item.deadline);
      });
    // NOLINTEND(boost-use-ranges)

    for (std::size_t i = 0U; i < 800U; i++) {
        summarize_futures(futures, success, failure, pending);
        if ((pending == 0U) || (now > (max_deadline + 2'000'000))) {
            return;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }
}

bool log_contains(const subscriber_log_t& log,
                  const std::size_t       receiver_node,
                  const std::size_t       topic_index,
                  const std::uint32_t     pub_id,
                  const std::uint64_t     seq)
{
    return log.unique.contains(std::make_tuple(receiver_node, topic_index, pub_id, seq));
}

d_case_result_t run_d_case(const d_case_config_t& cfg)
{
    TEST_ASSERT_TRUE((cfg.topic_count >= 2U) && (cfg.topic_count <= max_topics));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), cfg.seed));

    const e2e::fault_plan_t faults = build_fault_plan(cfg);
    if (faults.rules.empty()) {
        e2e::sim_net_faults_set(net, nullptr);
    } else {
        e2e::sim_net_faults_set(net, &faults);
    }

    d_case_result_t result{};
    handles_t       handles{};
    cy_us_t         now = 0;

    for (std::size_t t = 0U; t < cfg.topic_count; t++) {
        std::uint64_t parsed_hash = 0U;
        TEST_ASSERT_TRUE(topic_hash_from_pinned_literal(colliding_topics.at(t), parsed_hash));
        result.topic_hashes.at(t) = parsed_hash;
        result.preferred_subjects.at(t) =
          preferred_subject_id(e2e::sim_net_platform(net, e2e::sim_node_a), parsed_hash);
    }
    const std::uint32_t preferred0 = result.preferred_subjects.at(0U);
    for (std::size_t t = 1U; t < cfg.topic_count; t++) {
        TEST_ASSERT_EQUAL_UINT32(preferred0, result.preferred_subjects.at(t));
    }

    std::array<bool, max_topics> topic_active{};

    const auto ensure_topic_for_node = [&](const std::size_t node_index, const std::size_t topic_index) {
        if ((handles.pub.at(node_index).at(topic_index) != nullptr) ||
            (handles.sub.at(node_index).at(topic_index) != nullptr)) {
            TEST_ASSERT_NOT_NULL(handles.pub.at(node_index).at(topic_index));
            TEST_ASSERT_NOT_NULL(handles.sub.at(node_index).at(topic_index));
            return;
        }
        create_topic_handles(net, handles, result.log, node_index, topic_index, cfg.ordered_receiver);
    };

    const auto activate_topic_range = [&](const std::size_t first_topic, const std::size_t end_topic_exclusive) {
        for (std::size_t topic_index = first_topic; topic_index < end_topic_exclusive; topic_index++) {
            for (std::size_t node = 0U; node < e2e::sim_node_count; node++) {
                ensure_topic_for_node(node, topic_index);
            }
            topic_active.at(topic_index) = true;
        }
    };

    activate_topic_range(0U, 1U);

    std::size_t migration_capture_index = std::numeric_limits<std::size_t>::max();

    if (cfg.collision_while_idle) {
        drive_for(net, now, 200'000);
        activate_topic_range(1U, cfg.topic_count);
    }

    drive_for(net, now, 120'000);

    std::vector<future_state_t> futures{};

    if (!cfg.collision_while_idle) {
        // Emit one guaranteed pre-migration frame on the preferred subject before colliders are introduced.
        futures.push_back(publish_reliable(handles, e2e::sim_node_a, 0U, now));
        drive_for(net, now, 120'000);
        const auto first_pre =
          first_subject_for_hash(e2e::sim_net_captures(net), e2e::sim_node_a, result.topic_hashes.at(0U), 0U);
        TEST_ASSERT_TRUE(first_pre.has_value());
        TEST_ASSERT_EQUAL_UINT32(result.preferred_subjects.at(0U), *first_pre);
    }

    if (cfg.rounds > 0U) {
        const std::size_t migration_round = std::max<std::size_t>(1U, cfg.rounds / 3U);
        for (std::size_t round = 0U; round < cfg.rounds; round++) {
            if (!cfg.collision_while_idle && (migration_capture_index == std::numeric_limits<std::size_t>::max()) &&
                (round >= migration_round)) {
                activate_topic_range(1U, cfg.topic_count);
                migration_capture_index = e2e::sim_net_captures(net).size();
                inject_divergent_gossip(net,
                                        e2e::sim_node_a,
                                        UINT64_C(0xB0000000) + round,
                                        result.topic_hashes.at(0U),
                                        9U,
                                        colliding_topics.at(0U),
                                        now);
                inject_divergent_gossip(net,
                                        e2e::sim_node_b,
                                        UINT64_C(0xC0000000) + round,
                                        result.topic_hashes.at(0U),
                                        9U,
                                        colliding_topics.at(0U),
                                        now);
                drive_for(net, now, 100'000);
            }

            if (cfg.receiver_restart_rejoin && (round == (cfg.rounds / 2U))) {
                destroy_node_handles(net, handles, e2e::sim_node_b, cfg.topic_count, now);
                for (std::size_t t = 0U; t < cfg.topic_count; t++) {
                    if (topic_active.at(t)) {
                        ensure_topic_for_node(e2e::sim_node_b, t);
                    }
                }
                drive_for(net, now, 120'000);
            }

            if (cfg.gossip_churn && ((round % 2U) == 0U)) {
                for (std::size_t t = 0U; t < cfg.topic_count; t++) {
                    if (!topic_active.at(t)) {
                        continue;
                    }
                    inject_divergent_gossip(net,
                                            e2e::sim_node_a,
                                            UINT64_C(0x90000000) + round,
                                            result.topic_hashes.at(t),
                                            static_cast<std::uint32_t>(round + t + 1U),
                                            colliding_topics.at(t),
                                            now);
                    inject_divergent_gossip(net,
                                            e2e::sim_node_b,
                                            UINT64_C(0xA0000000) + round,
                                            result.topic_hashes.at(t),
                                            static_cast<std::uint32_t>(round + t + 2U),
                                            colliding_topics.at(t),
                                            now);
                }
            }

            const std::size_t concurrent = cfg.multi_future ? cfg.concurrent : 1U;
            for (std::size_t t = 0U; t < cfg.topic_count; t++) {
                if (!topic_active.at(t)) {
                    continue;
                }
                for (std::size_t i = 0U; i < concurrent; i++) {
                    futures.push_back(publish_reliable(handles, e2e::sim_node_a, t, now));
                }
                if ((round % 2U) == 0U) {
                    (void)publish_best_effort(handles, e2e::sim_node_b, t, now);
                }
            }

            TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
            now += step_us;
        }
    }

    if (!cfg.collision_while_idle) {
        TEST_ASSERT_TRUE(migration_capture_index != std::numeric_limits<std::size_t>::max());
    }

    drive_for(net, now, 2'500'000);

    wait_futures(net, now, futures, result.success_futures, result.failed_futures, result.pending_futures);
    TEST_ASSERT_EQUAL_size_t(0U, result.pending_futures);
    if (!futures.empty()) {
        TEST_ASSERT_TRUE(result.success_futures > 0U);
        if (!cfg.allow_future_failures) {
            TEST_ASSERT_EQUAL_size_t(0U, result.failed_futures);
        }
    }

    for (std::size_t t = 0U; t < cfg.topic_count; t++) {
        TEST_ASSERT_TRUE(topic_active.at(t));
        const std::uint64_t runtime_hash =
          topic_hash_for(e2e::sim_net_cy(net, e2e::sim_node_a), colliding_topics.at(t));
        TEST_ASSERT_EQUAL_UINT64(result.topic_hashes.at(t), runtime_hash);
    }

    for (std::size_t node = 0U; node < e2e::sim_node_count; node++) {
        for (std::size_t t = 0U; t < cfg.topic_count; t++) {
            (void)publish_best_effort(handles, node, t, now);
        }
    }
    drive_for(net, now, 200'000);

    for (std::size_t t = 0U; t < cfg.topic_count; t++) {
        const auto final_a =
          last_subject_for_hash(e2e::sim_net_captures(net), e2e::sim_node_a, result.topic_hashes.at(t));
        const auto final_b =
          last_subject_for_hash(e2e::sim_net_captures(net), e2e::sim_node_b, result.topic_hashes.at(t));
        TEST_ASSERT_TRUE(final_a.has_value());
        TEST_ASSERT_TRUE(final_b.has_value());
        TEST_ASSERT_EQUAL_UINT32(*final_a, *final_b);
        result.final_subjects.at(t) = *final_a;
    }

    std::set<std::uint32_t> final_unique{};
    bool                    migrated     = false;
    bool                    transitioned = false;
    for (std::size_t t = 0U; t < cfg.topic_count; t++) {
        final_unique.insert(result.final_subjects.at(t));
        migrated     = migrated || (result.final_subjects.at(t) != result.preferred_subjects.at(t));
        transitioned = transitioned || (distinct_subject_count_for_hash(
                                          e2e::sim_net_captures(net), e2e::sim_node_a, result.topic_hashes.at(t)) > 1U);
    }
    TEST_ASSERT_EQUAL_size_t(cfg.topic_count, final_unique.size());
    TEST_ASSERT_TRUE(migrated);
    if (cfg.require_transition_observed) {
        TEST_ASSERT_TRUE(transitioned);
        const auto first_pre =
          first_subject_for_hash(e2e::sim_net_captures(net), e2e::sim_node_a, result.topic_hashes.at(0U), 0U);
        TEST_ASSERT_TRUE(first_pre.has_value());
        TEST_ASSERT_EQUAL_UINT32(result.preferred_subjects.at(0U), *first_pre);
        TEST_ASSERT_TRUE(result.final_subjects.at(0U) != result.preferred_subjects.at(0U));
    }

    if (cfg.stale_old_subject_replay) {
        std::optional<std::size_t> moved_topic{};
        for (std::size_t t = 0U; t < cfg.topic_count; t++) {
            if (result.final_subjects.at(t) != result.preferred_subjects.at(t)) {
                moved_topic = t;
                break;
            }
        }
        TEST_ASSERT_TRUE(moved_topic.has_value());

        std::optional<e2e::frame_info_t> stale_frame{};
        for (const e2e::frame_capture_t& cap : e2e::sim_net_captures(net)) {
            if ((cap.frame.source != e2e::sim_node_a) || (cap.frame.destination != e2e::sim_node_b) ||
                !is_message_frame(cap.frame) || !cap.frame.has_topic_hash ||
                (cap.frame.topic_hash != result.topic_hashes.at(*moved_topic)) ||
                (cap.frame.subject_id != result.preferred_subjects.at(*moved_topic))) {
                continue;
            }
            e2e::app_payload_t payload{};
            if (!e2e::app_payload_unpack(cap.frame.payload, payload)) {
                continue;
            }
            if (log_contains(result.log, e2e::sim_node_b, *moved_topic, payload.publisher_id, payload.sequence)) {
                stale_frame = cap.frame;
                break;
            }
        }
        TEST_ASSERT_TRUE(stale_frame.has_value());

        const std::size_t   before = result.log.unique.size();
        e2e::queued_frame_t replay{};
        replay.frame              = *stale_frame;
        replay.frame.deliver_time = now + 1;
        replay.frame.sequence     = stale_frame->sequence + UINT64_C(0x100000);
        net.queue.push_back(replay);

        drive_for(net, now, 120'000);
        TEST_ASSERT_EQUAL_size_t(before, result.log.unique.size());
    }

    TEST_ASSERT_EQUAL_size_t(0U, result.log.malformed_count);
    TEST_ASSERT_EQUAL_size_t(0U, result.log.duplicate_count);
    for (std::size_t t = 0U; t < cfg.topic_count; t++) {
        const std::size_t slot = pub_id_for(e2e::sim_node_a, t) % max_pub_slots;
        TEST_ASSERT_TRUE(result.log.count.at(e2e::sim_node_b).at(t).at(slot) > 0U);
    }

    destroy_futures(futures);
    destroy_all_handles(net, handles, cfg.topic_count, now);

    drain_queue(net, now);
    e2e::assert_quiescent(net);
    e2e::sim_net_deinit(net);
    e2e::assert_all_heaps_clean(net);
    e2e::assert_no_live_messages();
    return result;
}

d_case_config_t base_cfg()
{
    d_case_config_t cfg{};
    cfg.topic_count = 2U;
    cfg.rounds      = 12U;
    cfg.concurrent  = 1U;
    return cfg;
}

void test_api_pubsub_e2e_d01_collision_introduced_while_idle_convergence_check()
{
    d_case_config_t cfg             = base_cfg();
    cfg.collision_while_idle        = true;
    cfg.require_transition_observed = false;
    cfg.rounds                      = 0U;
    cfg.seed                        = 0xD01U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_EQUAL_size_t(0U, res.success_futures);
    TEST_ASSERT_EQUAL_size_t(0U, res.failed_futures);
}

void test_api_pubsub_e2e_d02_collision_during_live_reliable_stream_no_faults()
{
    d_case_config_t cfg = base_cfg();
    cfg.seed            = 0xD02U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
}

void test_api_pubsub_e2e_d03_d02_plus_transient_data_loss()
{
    d_case_config_t cfg = base_cfg();
    cfg.drop_data       = true;
    cfg.seed            = 0xD03U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
}

void test_api_pubsub_e2e_d04_d02_plus_transient_ack_loss()
{
    d_case_config_t cfg = base_cfg();
    cfg.drop_ack        = true;
    cfg.seed            = 0xD04U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
}

void test_api_pubsub_e2e_d05_mixed_faults_data_ack_reorder()
{
    d_case_config_t cfg = base_cfg();
    cfg.drop_data       = true;
    cfg.drop_ack        = true;
    cfg.reorder         = true;
    cfg.seed            = 0xD05U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
}

void test_api_pubsub_e2e_d06_d05_ordered_subscriber_variant()
{
    d_case_config_t cfg  = base_cfg();
    cfg.drop_data        = true;
    cfg.drop_ack         = true;
    cfg.reorder          = true;
    cfg.ordered_receiver = true;
    cfg.seed             = 0xD06U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
}

void test_api_pubsub_e2e_d07_d05_unordered_subscriber_variant()
{
    d_case_config_t cfg  = base_cfg();
    cfg.drop_data        = true;
    cfg.drop_ack         = true;
    cfg.reorder          = true;
    cfg.ordered_receiver = false;
    cfg.seed             = 0xD07U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
}

void test_api_pubsub_e2e_d08_migration_with_multiple_concurrent_futures()
{
    d_case_config_t cfg = base_cfg();
    cfg.multi_future    = true;
    cfg.concurrent      = 6U;
    cfg.rounds          = 8U;
    cfg.seed            = 0xD08U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 20U);
}

void test_api_pubsub_e2e_d09_divergent_gossip_churn_eventual_stability()
{
    d_case_config_t cfg       = base_cfg();
    cfg.gossip_churn          = true;
    cfg.rounds                = 14U;
    cfg.allow_future_failures = true;
    cfg.seed                  = 0xD09U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
}

void test_api_pubsub_e2e_d10_multi_collision_displacement_chain_live_stream()
{
    d_case_config_t cfg       = base_cfg();
    cfg.topic_count           = 3U;
    cfg.multi_future          = true;
    cfg.concurrent            = 3U;
    cfg.rounds                = 10U;
    cfg.allow_future_failures = true;
    cfg.seed                  = 0xD10U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
}

void test_api_pubsub_e2e_d11_stale_old_subject_frames_do_not_disturb_application()
{
    d_case_config_t cfg          = base_cfg();
    cfg.drop_data                = true;
    cfg.drop_ack                 = true;
    cfg.reorder                  = true;
    cfg.stale_old_subject_replay = true;
    cfg.allow_future_failures    = true;
    cfg.seed                     = 0xD11U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
}

void test_api_pubsub_e2e_d12_receiver_restart_rejoin_during_migration()
{
    d_case_config_t cfg         = base_cfg();
    cfg.drop_data               = true;
    cfg.drop_ack                = true;
    cfg.reorder                 = true;
    cfg.receiver_restart_rejoin = true;
    cfg.rounds                  = 14U;
    cfg.allow_future_failures   = true;
    cfg.seed                    = 0xD12U;

    const d_case_result_t res = run_d_case(cfg);
    TEST_ASSERT_TRUE(res.success_futures > 0U);
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
    RUN_TEST(test_api_pubsub_e2e_d01_collision_introduced_while_idle_convergence_check);
    RUN_TEST(test_api_pubsub_e2e_d02_collision_during_live_reliable_stream_no_faults);
    RUN_TEST(test_api_pubsub_e2e_d03_d02_plus_transient_data_loss);
    RUN_TEST(test_api_pubsub_e2e_d04_d02_plus_transient_ack_loss);
    RUN_TEST(test_api_pubsub_e2e_d05_mixed_faults_data_ack_reorder);
    RUN_TEST(test_api_pubsub_e2e_d06_d05_ordered_subscriber_variant);
    RUN_TEST(test_api_pubsub_e2e_d07_d05_unordered_subscriber_variant);
    RUN_TEST(test_api_pubsub_e2e_d08_migration_with_multiple_concurrent_futures);
    RUN_TEST(test_api_pubsub_e2e_d09_divergent_gossip_churn_eventual_stability);
    RUN_TEST(test_api_pubsub_e2e_d10_multi_collision_displacement_chain_live_stream);
    RUN_TEST(test_api_pubsub_e2e_d11_stale_old_subject_frames_do_not_disturb_application);
    RUN_TEST(test_api_pubsub_e2e_d12_receiver_restart_rejoin_during_migration);
    return UNITY_END();
}
