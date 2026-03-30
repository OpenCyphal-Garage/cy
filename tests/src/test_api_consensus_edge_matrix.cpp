#include <cy_platform.h>
#include <unity.h>
#include "e2e_faults.hpp"
#include "e2e_sim_net.hpp"
#include "e2e_scenario_utils.hpp"
#include "e2e_test_utils.hpp"
#include "helpers.h"
#include "message.h"
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace {

constexpr cy_us_t      step_us             = 1'000;
constexpr cy_us_t      publish_deadline_us = 200'000;
constexpr cy_us_t      expiry_timeout_us   = 600'000'000;
constexpr std::uint8_t header_gossip       = 8U;

using e2e::arrival_capture_t;
using e2e::count_by_publisher;
using e2e::on_arrival_capture;

void cleanup_case(e2e::sim_net_t&                     net,
                  cy_us_t&                            now,
                  const std::vector<cy_future_t*>&    subscribers,
                  const std::vector<cy_publisher_t*>& publishers)
{
    e2e::cleanup_case(net, now, {}, subscribers, publishers, step_us, 100'000, 100'000U);
}

void publish_best_effort(cy_publisher_t* const pub,
                         const std::uint32_t   publisher_id,
                         const std::uint64_t   sequence,
                         const cy_us_t         now)
{
    const auto       payload = e2e::app_payload_pack(publisher_id, sequence);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, now + publish_deadline_us, msg));
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
      make_gossip_header(wire.data(), wire.size(), 3U, -1, topic_hash, evictions, cy_str(topic_name));
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

bool topic_exists_by_hash_iter(const cy_t* const cy, const std::uint64_t topic_hash)
{
    for (cy_topic_t* topic = cy_topic_iter_first(cy); topic != nullptr; topic = cy_topic_iter_next(topic)) {
        if (cy_topic_hash(topic) == topic_hash) {
            return true;
        }
    }
    return false;
}

std::size_t count_gossip_frames_for_hash_from_nodes(const std::vector<e2e::frame_capture_t>& captures,
                                                    const std::size_t                        start_index,
                                                    const std::uint64_t                      topic_hash,
                                                    const std::size_t                        node_a,
                                                    const std::size_t                        node_b)
{
    std::size_t count = 0U;
    for (std::size_t i = start_index; i < captures.size(); i++) {
        const e2e::frame_capture_t& cap = captures.at(i);
        if (!cap.frame.has_topic_hash || (cap.frame.topic_hash != topic_hash) ||
            (cap.frame.header_type != header_gossip)) {
            continue;
        }
        if ((cap.frame.source == node_a) || (cap.frame.source == node_b)) {
            count++;
        }
    }
    return count;
}

void test_api_consensus_edge_partition_heal_eventual_bidirectional_delivery()
{
    constexpr std::uint32_t pub_id_a       = 4101U;
    constexpr std::uint32_t pub_id_b       = 4102U;
    constexpr cy_us_t       partition_from = 0;
    constexpr cy_us_t       partition_to   = 180'000;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(
      faults,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_a, e2e::sim_node_b),
                                    e2e::fault_predicate_send_time(partition_from, partition_to) }));
    e2e::fault_plan_add_drop(
      faults,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_direction(e2e::sim_node_b, e2e::sim_node_a),
                                    e2e::fault_predicate_send_time(partition_from, partition_to) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xE001)));
    e2e::sim_net_faults_set(net, &faults);

    cy_publisher_t* const pub_a =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/consensus/partition/topic"));
    cy_publisher_t* const pub_b =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("e2e/consensus/partition/topic"));
    TEST_ASSERT_NOT_NULL(pub_a);
    TEST_ASSERT_NOT_NULL(pub_b);

    arrival_capture_t capture_a{};
    arrival_capture_t capture_b{};

    cy_future_t* const sub_a =
      cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/consensus/partition/topic"), 64U);
    cy_future_t* const sub_b =
      cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("e2e/consensus/partition/topic"), 64U);
    TEST_ASSERT_NOT_NULL(sub_a);
    TEST_ASSERT_NOT_NULL(sub_b);

    cy_user_context_t ctx_a = CY_USER_CONTEXT_EMPTY;
    ctx_a.ptr[0]            = &capture_a;
    cy_future_context_set(sub_a, ctx_a);
    cy_future_callback_set(sub_a, on_arrival_capture);

    cy_user_context_t ctx_b = CY_USER_CONTEXT_EMPTY;
    ctx_b.ptr[0]            = &capture_b;
    cy_future_context_set(sub_b, ctx_b);
    cy_future_callback_set(sub_b, on_arrival_capture);

    cy_us_t now = 0;
    for (std::uint64_t seq = 1U; seq <= 36U; seq++) {
        e2e::set_now(net, now);
        publish_best_effort(pub_a, pub_id_a, seq, now);
        publish_best_effort(pub_b, pub_id_b, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }

    e2e::drive_for(net, now, 350'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture_a.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, capture_b.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_a, pub_id_b) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(capture_b, pub_id_a) > 0U);

    cleanup_case(net, now, { sub_a, sub_b }, { pub_a, pub_b });
}

void test_api_consensus_edge_colliding_topics_discover_and_deliver_with_faults()
{
    constexpr std::uint32_t pub_id_a = 4201U;
    constexpr std::uint32_t pub_id_b = 4202U;

    static constexpr const char* topic_a = "e2e/consensus/collide/a_0";
    static constexpr const char* topic_b = "e2e/consensus/collide/b_19583";
    static constexpr const char* pattern = "e2e/consensus/collide/>";

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(
      faults,
      25'000,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(7U), e2e::fault_predicate_every_nth(3U) }));
    e2e::fault_plan_add_duplicate(
      faults,
      1U,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(7U), e2e::fault_predicate_every_nth(7U) }));
    e2e::fault_plan_add_delay(
      faults,
      3'000,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(0U), e2e::fault_predicate_every_nth(4U) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xE002)));
    e2e::sim_net_faults_set(net, &faults);

    cy_future_t* const sub_a = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(pattern), 64U);
    cy_future_t* const sub_b = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(pattern), 64U);
    TEST_ASSERT_NOT_NULL(sub_a);
    TEST_ASSERT_NOT_NULL(sub_b);

    arrival_capture_t capture_a{};
    arrival_capture_t capture_b{};

    cy_user_context_t ctx_a = CY_USER_CONTEXT_EMPTY;
    ctx_a.ptr[0]            = &capture_a;
    cy_future_context_set(sub_a, ctx_a);
    cy_future_callback_set(sub_a, on_arrival_capture);

    cy_user_context_t ctx_b = CY_USER_CONTEXT_EMPTY;
    ctx_b.ptr[0]            = &capture_b;
    cy_future_context_set(sub_b, ctx_b);
    cy_future_callback_set(sub_b, on_arrival_capture);

    cy_publisher_t* const pub_a = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(topic_a));
    cy_publisher_t* const pub_b = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_b));
    TEST_ASSERT_NOT_NULL(pub_a);
    TEST_ASSERT_NOT_NULL(pub_b);

    cy_us_t now = 0;
    e2e::drive_for(net, now, 800'000, step_us);

    const cy_topic_t* const a_topic_a = cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(topic_a));
    const cy_topic_t* const a_topic_b = cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(topic_b));
    const cy_topic_t* const b_topic_a = cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_a));
    const cy_topic_t* const b_topic_b = cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_b));
    TEST_ASSERT_NOT_NULL(a_topic_a);
    TEST_ASSERT_NOT_NULL(a_topic_b);
    TEST_ASSERT_NOT_NULL(b_topic_a);
    TEST_ASSERT_NOT_NULL(b_topic_b);

    const std::uint64_t hash_a = cy_topic_hash(a_topic_a);
    const std::uint64_t hash_b = cy_topic_hash(a_topic_b);
    TEST_ASSERT_TRUE(hash_a != hash_b);

    for (std::uint64_t seq = 1U; seq <= 24U; seq++) {
        e2e::set_now(net, now);
        publish_best_effort(pub_a, pub_id_a, seq, now);
        publish_best_effort(pub_b, pub_id_b, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 12'000;
    }
    e2e::drive_for(net, now, 400'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture_a.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, capture_b.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_a, pub_id_b) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(capture_b, pub_id_a) > 0U);

    cleanup_case(net, now, { sub_a, sub_b }, { pub_a, pub_b });
}

void test_api_consensus_edge_implicit_topics_do_not_keep_each_other_alive()
{
    constexpr std::size_t        node_count        = 3U;
    constexpr std::size_t        publisher_node    = 0U;
    constexpr std::size_t        subscriber_node_a = 1U;
    constexpr std::size_t        subscriber_node_b = 2U;
    constexpr std::uint32_t      publisher_id      = 4301U;
    static constexpr const char* topic_name        = "foo/bar";
    static constexpr const char* topic_pattern     = ">";

    e2e::sim_net_config_t cfg{};
    cfg.node_count       = node_count;
    cfg.random_seed_base = UINT64_C(0xE003);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    arrival_capture_t capture_a{};
    arrival_capture_t capture_b{};

    cy_future_t* const sub_a = cy_subscribe(e2e::sim_net_cy(net, subscriber_node_a), cy_str(topic_pattern), 64U);
    cy_future_t* const sub_b = cy_subscribe(e2e::sim_net_cy(net, subscriber_node_b), cy_str(topic_pattern), 64U);
    TEST_ASSERT_NOT_NULL(sub_a);
    TEST_ASSERT_NOT_NULL(sub_b);

    cy_user_context_t ctx_a = CY_USER_CONTEXT_EMPTY;
    ctx_a.ptr[0]            = &capture_a;
    cy_future_context_set(sub_a, ctx_a);
    cy_future_callback_set(sub_a, on_arrival_capture);

    cy_user_context_t ctx_b = CY_USER_CONTEXT_EMPTY;
    ctx_b.ptr[0]            = &capture_b;
    cy_future_context_set(sub_b, ctx_b);
    cy_future_callback_set(sub_b, on_arrival_capture);

    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, publisher_node), cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(pub);
    const std::uint64_t topic_hash = cy_topic_hash(cy_publisher_topic(pub));

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, 400'000, step_us);

    for (std::uint64_t seq = 1U; seq <= 16U; seq++) {
        e2e::set_now_all(net, now);
        publish_best_effort(pub, publisher_id, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round_all(net, now));
        now += 10'000;
    }
    e2e::drive_for_all(net, now, 300'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture_a.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, capture_b.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_a, publisher_id) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(capture_b, publisher_id) > 0U);
    TEST_ASSERT_TRUE(topic_exists_by_hash_iter(e2e::sim_net_cy(net, subscriber_node_a), topic_hash));
    TEST_ASSERT_TRUE(topic_exists_by_hash_iter(e2e::sim_net_cy(net, subscriber_node_b), topic_hash));

    cy_unadvertise(pub);
    e2e::drive_for_all(net, now, 200'000, step_us);

    const std::size_t capture_start_no_gossip = e2e::sim_net_captures(net).size();
    e2e::drive_for_all(net, now, 15'000'000, 50'000);
    TEST_ASSERT_EQUAL_size_t(
      0U,
      count_gossip_frames_for_hash_from_nodes(
        e2e::sim_net_captures(net), capture_start_no_gossip, topic_hash, subscriber_node_a, subscriber_node_b));

    const std::size_t capture_start_corrective = e2e::sim_net_captures(net).size();
    inject_divergent_gossip(net, subscriber_node_a, UINT64_C(0xABCD0001), topic_hash, 1U, topic_name, now);
    e2e::drive_for_all(net, now, 300'000, step_us);
    TEST_ASSERT_TRUE(
      count_gossip_frames_for_hash_from_nodes(
        e2e::sim_net_captures(net), capture_start_corrective, topic_hash, subscriber_node_a, subscriber_node_b) > 0U);

    e2e::drive_for_all(net, now, expiry_timeout_us + 20'000'000, 5'000'000);
    TEST_ASSERT_FALSE(topic_exists_by_hash_iter(e2e::sim_net_cy(net, subscriber_node_a), topic_hash));
    TEST_ASSERT_FALSE(topic_exists_by_hash_iter(e2e::sim_net_cy(net, subscriber_node_b), topic_hash));

    cleanup_case(net, now, { sub_a, sub_b }, {});
}

void test_api_consensus_edge_implicit_topic_expiry_large_time_jump_with_ordered_subscriber()
{
    constexpr std::size_t        node_count      = 2U;
    constexpr std::size_t        publisher_node  = 0U;
    constexpr std::size_t        subscriber_node = 1U;
    constexpr std::uint32_t      publisher_id    = 4401U;
    static constexpr const char* topic_name      = "foo/bar";
    static constexpr const char* topic_pattern   = ">";

    e2e::sim_net_config_t cfg{};
    cfg.node_count       = node_count;
    cfg.random_seed_base = UINT64_C(0xE004);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    arrival_capture_t capture{};

    cy_future_t* const sub = cy_subscribe_ordered(
      e2e::sim_net_cy(net, subscriber_node), cy_str(topic_pattern), 64U, expiry_timeout_us + 100'000'000);
    TEST_ASSERT_NOT_NULL(sub);
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &capture;
    cy_future_context_set(sub, ctx);
    cy_future_callback_set(sub, on_arrival_capture);

    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, publisher_node), cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(pub);
    const std::uint64_t topic_hash = cy_topic_hash(cy_publisher_topic(pub));

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, 200'000, step_us);
    e2e::set_now_all(net, now);
    publish_best_effort(pub, publisher_id, 1U, now);
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round_all(net, now));
    now += 10'000;
    e2e::drive_for_all(net, now, 50'000, step_us); // Keep the message queued inside reordering.

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, capture.samples.size());
    TEST_ASSERT_TRUE(topic_exists_by_hash_iter(e2e::sim_net_cy(net, subscriber_node), topic_hash));

    cy_unadvertise(pub);
    e2e::drive_for_all(net, now, 10'000, step_us);

    // Adversarial jump: advance directly beyond implicit timeout in one spin.
    now += expiry_timeout_us + 5'000'000;
    e2e::set_now_all(net, now);
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round_all(net, now));

    // Retiring the topic should decouple and flush the queued ordered state via reordering_eject_all().
    TEST_ASSERT_TRUE(count_by_publisher(capture, publisher_id) > 0U);
    TEST_ASSERT_FALSE(topic_exists_by_hash_iter(e2e::sim_net_cy(net, subscriber_node), topic_hash));
    cleanup_case(net, now, { sub }, {});
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
    RUN_TEST(test_api_consensus_edge_partition_heal_eventual_bidirectional_delivery);
    RUN_TEST(test_api_consensus_edge_colliding_topics_discover_and_deliver_with_faults);
    RUN_TEST(test_api_consensus_edge_implicit_topics_do_not_keep_each_other_alive);
    RUN_TEST(test_api_consensus_edge_implicit_topic_expiry_large_time_jump_with_ordered_subscriber);
    return UNITY_END();
}
