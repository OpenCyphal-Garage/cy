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
#include <ranges>
#include <vector>

namespace {

constexpr cy_us_t step_us             = 1'000;
constexpr cy_us_t publish_deadline_us = 200'000;

struct arrival_sample_t final
{
    std::uint32_t publisher_id{ 0U };
    std::uint64_t sequence{ 0U };
    std::uint64_t topic_hash{ 0U };
};

struct arrival_capture_t final
{
    std::vector<arrival_sample_t> samples{};
    std::size_t                   malformed{ 0U };
};

extern "C" void on_arrival_capture(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }

    auto* const capture = static_cast<arrival_capture_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(capture);

    std::array<unsigned char, 32> bytes{};
    const std::size_t             size = cy_message_read(arrival.message.content, 0U, bytes.size(), bytes.data());

    e2e::app_payload_t payload{};
    if (!e2e::app_payload_unpack(bytes.data(), size, payload)) {
        capture->malformed++;
        cy_message_refcount_dec(arrival.message.content);
        return;
    }

    capture->samples.push_back(arrival_sample_t{
      .publisher_id = payload.publisher_id,
      .sequence     = payload.sequence,
      .topic_hash   = arrival.breadcrumb.topic_hash,
    });
    cy_message_refcount_dec(arrival.message.content);
}

void set_now(e2e::sim_net_t& net, const cy_us_t now)
{
    e2e::sim_net_node_now_set(net, e2e::sim_node_a, now);
    e2e::sim_net_node_now_set(net, e2e::sim_node_b, now);
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
        TEST_ASSERT_TRUE(guard < 100'000U);
    }
}

void cleanup_case(e2e::sim_net_t&                     net,
                  cy_us_t&                            now,
                  const std::vector<cy_future_t*>&    subscribers,
                  const std::vector<cy_publisher_t*>& publishers)
{
    for (cy_future_t* const sub : subscribers) {
        if (sub != nullptr) {
            cy_future_destroy(sub);
        }
    }
    drive_for(net, now, 100'000);

    for (cy_publisher_t* const pub : publishers) {
        if (pub != nullptr) {
            cy_unadvertise(pub);
        }
    }
    drive_for(net, now, 100'000);

    drain_queue(net, now);
    e2e::assert_quiescent(net);

    e2e::sim_net_deinit(net);
    e2e::assert_all_node_heaps_clean(net);
    e2e::assert_no_live_messages();
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

std::size_t count_by_publisher(const arrival_capture_t& capture, const std::uint32_t publisher_id)
{
    const auto count = std::ranges::count_if(
      capture.samples, [publisher_id](const arrival_sample_t& sample) { return sample.publisher_id == publisher_id; });
    return static_cast<std::size_t>(count);
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
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), UINT64_C(0xE001)));
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
        set_now(net, now);
        publish_best_effort(pub_a, pub_id_a, seq, now);
        publish_best_effort(pub_b, pub_id_b, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }

    drive_for(net, now, 350'000);

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

    static constexpr const char* topic_a = "e2e/consensus/collide/a/#1000000000001000";
    static constexpr const char* topic_b = "e2e/consensus/collide/b/#10000000007feff3";
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
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), UINT64_C(0xE002)));
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
    drive_for(net, now, 800'000);

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
        set_now(net, now);
        publish_best_effort(pub_a, pub_id_a, seq, now);
        publish_best_effort(pub_b, pub_id_b, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 12'000;
    }
    drive_for(net, now, 400'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture_a.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, capture_b.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_a, pub_id_b) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(capture_b, pub_id_a) > 0U);

    cleanup_case(net, now, { sub_a, sub_b }, { pub_a, pub_b });
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
    return UNITY_END();
}
