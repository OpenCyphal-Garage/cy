// Verify that pinning a topic does not affect pattern matching.
// Pinned topics (name#decimal) must be discovered and delivered by pattern subscribers (*, >)
// exactly like unpinned topics.

#include <cy_platform.h>
#include <unity.h>
#include "e2e_sim_net.hpp"
#include "e2e_scenario_utils.hpp"
#include "e2e_test_utils.hpp"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string>
#include <vector>

namespace {

constexpr cy_us_t step_us          = 1'000;
constexpr cy_us_t publish_deadline = 200'000;
constexpr cy_us_t converge_time    = 800'000;
constexpr cy_us_t delivery_time    = 400'000;

using e2e::arrival_capture_t;
using e2e::count_by_publisher;
using e2e::on_arrival_capture;

void publish_best_effort(cy_publisher_t* const pub,
                         const std::uint32_t   publisher_id,
                         const std::uint64_t   sequence,
                         const cy_us_t         now)
{
    const auto       payload = e2e::app_payload_pack(publisher_id, sequence);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, now + publish_deadline, msg));
}

cy_future_t* make_pattern_sub(cy_t* const cy, const char* const pattern, arrival_capture_t& capture)
{
    cy_future_t* const sub = cy_subscribe(cy, cy_str(pattern), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &capture;
    cy_future_context_set(sub, ctx);
    cy_future_callback_set(sub, on_arrival_capture);
    return sub;
}

// ---------------------------------------------------------------------------
// Test 1: Pinned topic matches '>' pattern.
// ---------------------------------------------------------------------------
void test_pinned_topic_matches_chevron_pattern()
{
    constexpr std::uint32_t pub_id = 5001U;

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xA101)));

    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/pin/alpha#100"));
    TEST_ASSERT_NOT_NULL(pub);

    arrival_capture_t  capture{};
    cy_future_t* const sub = make_pattern_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "e2e/pin/>", capture);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    for (std::uint64_t seq = 1U; seq <= 16U; seq++) {
        e2e::set_now(net, now);
        publish_best_effort(pub, pub_id, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture, pub_id) > 0U);

    // The pinned topic should be discoverable by its stored name (without the pin suffix).
    const cy_topic_t* const topic =
      cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("e2e/pin/alpha"));
    TEST_ASSERT_NOT_NULL(topic);

    e2e::cleanup_case(net, now, {}, { sub }, { pub }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test 2: Pinned topic matches '*' pattern.
// ---------------------------------------------------------------------------
void test_pinned_topic_matches_star_pattern()
{
    constexpr std::uint32_t pub_id = 5002U;

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xA102)));

    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/pin/star/alpha#300"));
    TEST_ASSERT_NOT_NULL(pub);

    arrival_capture_t  capture{};
    cy_future_t* const sub = make_pattern_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "e2e/pin/star/*", capture);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    for (std::uint64_t seq = 1U; seq <= 16U; seq++) {
        e2e::set_now(net, now);
        publish_best_effort(pub, pub_id, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture, pub_id) > 0U);

    const cy_topic_t* const topic =
      cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("e2e/pin/star/alpha"));
    TEST_ASSERT_NOT_NULL(topic);

    e2e::cleanup_case(net, now, {}, { sub }, { pub }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test 3: Mixed pinned and unpinned topics all match the same '>' pattern.
// ---------------------------------------------------------------------------
void test_mixed_pinned_unpinned_all_match_same_pattern()
{
    constexpr std::uint32_t pub_id_pinned   = 5003U;
    constexpr std::uint32_t pub_id_unpinned = 5004U;

    constexpr std::size_t publisher_node_a = 0U;
    constexpr std::size_t publisher_node_b = 1U;
    constexpr std::size_t subscriber_node  = 2U;

    e2e::sim_net_config_t cfg{};
    cfg.node_count       = 3U;
    cfg.random_seed_base = UINT64_C(0xA103);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    cy_publisher_t* const pub_a = cy_advertise(e2e::sim_net_cy(net, publisher_node_a), cy_str("e2e/pin/mix/alpha#100"));
    cy_publisher_t* const pub_b = cy_advertise(e2e::sim_net_cy(net, publisher_node_b), cy_str("e2e/pin/mix/beta"));
    TEST_ASSERT_NOT_NULL(pub_a);
    TEST_ASSERT_NOT_NULL(pub_b);

    arrival_capture_t  capture{};
    cy_future_t* const sub = make_pattern_sub(e2e::sim_net_cy(net, subscriber_node), "e2e/pin/mix/>", capture);

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, converge_time, step_us);

    for (std::uint64_t seq = 1U; seq <= 16U; seq++) {
        e2e::set_now_all(net, now);
        publish_best_effort(pub_a, pub_id_pinned, seq, now);
        publish_best_effort(pub_b, pub_id_unpinned, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round_all(net, now));
        now += 10'000;
    }
    e2e::drive_for_all(net, now, delivery_time, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture, pub_id_pinned) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(capture, pub_id_unpinned) > 0U);

    // Both topics should be discoverable on the subscriber node by their stored names.
    TEST_ASSERT_NOT_NULL(cy_topic_find_by_name(e2e::sim_net_cy(net, subscriber_node), cy_str("e2e/pin/mix/alpha")));
    TEST_ASSERT_NOT_NULL(cy_topic_find_by_name(e2e::sim_net_cy(net, subscriber_node), cy_str("e2e/pin/mix/beta")));

    cy_future_destroy(sub);
    e2e::drive_for_all(net, now, 100'000, step_us);
    cy_unadvertise(pub_a);
    cy_unadvertise(pub_b);
    e2e::drive_for_all(net, now, 100'000, step_us);
    e2e::drain_queue_all(net, now, step_us, 100'000U);
    e2e::assert_quiescent(net);
    e2e::sim_net_deinit(net);
    e2e::assert_all_node_heaps_clean(net);
    e2e::assert_no_live_messages();
}

// ---------------------------------------------------------------------------
// Test 4: Multi-node cross-delivery with pinned and unpinned topics.
// Each node advertises a topic and subscribes to the same pattern.
// ---------------------------------------------------------------------------
void test_multinode_cross_pinned_pattern_delivery()
{
    constexpr std::size_t   node_count = 3U;
    constexpr std::uint32_t pub_id_0   = 5010U;
    constexpr std::uint32_t pub_id_1   = 5011U;
    constexpr std::uint32_t pub_id_2   = 5012U;

    static constexpr const char* topic_0 = "e2e/pin/cross/a#400";
    static constexpr const char* topic_1 = "e2e/pin/cross/b#500";
    static constexpr const char* topic_2 = "e2e/pin/cross/c";
    static constexpr const char* pattern = "e2e/pin/cross/>";

    // Stored names (without pin suffixes).
    static constexpr const char* stored_0 = "e2e/pin/cross/a";
    static constexpr const char* stored_1 = "e2e/pin/cross/b";
    static constexpr const char* stored_2 = "e2e/pin/cross/c";

    e2e::sim_net_config_t cfg{};
    cfg.node_count       = node_count;
    cfg.random_seed_base = UINT64_C(0xA104);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    cy_publisher_t* const pub_0 = cy_advertise(e2e::sim_net_cy(net, 0U), cy_str(topic_0));
    cy_publisher_t* const pub_1 = cy_advertise(e2e::sim_net_cy(net, 1U), cy_str(topic_1));
    cy_publisher_t* const pub_2 = cy_advertise(e2e::sim_net_cy(net, 2U), cy_str(topic_2));
    TEST_ASSERT_NOT_NULL(pub_0);
    TEST_ASSERT_NOT_NULL(pub_1);
    TEST_ASSERT_NOT_NULL(pub_2);

    std::array<arrival_capture_t, node_count> captures{};
    std::array<cy_future_t*, node_count>      subs{};
    for (std::size_t i = 0U; i < node_count; i++) {
        subs.at(i) = make_pattern_sub(e2e::sim_net_cy(net, i), pattern, captures.at(i));
    }

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, converge_time, step_us);

    for (std::uint64_t seq = 1U; seq <= 16U; seq++) {
        e2e::set_now_all(net, now);
        publish_best_effort(pub_0, pub_id_0, seq, now);
        publish_best_effort(pub_1, pub_id_1, seq, now);
        publish_best_effort(pub_2, pub_id_2, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round_all(net, now));
        now += 10'000;
    }
    e2e::drive_for_all(net, now, delivery_time, step_us);

    for (const auto& cap : captures) {
        TEST_ASSERT_EQUAL_size_t(0U, cap.malformed);
    }

    // Each node should receive messages from the other two publishers.
    TEST_ASSERT_TRUE(count_by_publisher(captures[0], pub_id_1) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(captures[0], pub_id_2) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(captures[1], pub_id_0) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(captures[1], pub_id_2) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(captures[2], pub_id_0) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(captures[2], pub_id_1) > 0U);

    // All stored topic names should be discoverable on every node.
    for (std::size_t i = 0U; i < node_count; i++) {
        const cy_t* const cy = e2e::sim_net_cy(net, i);
        TEST_ASSERT_NOT_NULL(cy_topic_find_by_name(cy, cy_str(stored_0)));
        TEST_ASSERT_NOT_NULL(cy_topic_find_by_name(cy, cy_str(stored_1)));
        TEST_ASSERT_NOT_NULL(cy_topic_find_by_name(cy, cy_str(stored_2)));
    }

    for (auto& sub : subs) {
        cy_future_destroy(sub);
    }
    e2e::drive_for_all(net, now, 100'000, step_us);
    cy_unadvertise(pub_0);
    cy_unadvertise(pub_1);
    cy_unadvertise(pub_2);
    e2e::drive_for_all(net, now, 100'000, step_us);
    e2e::drain_queue_all(net, now, step_us, 100'000U);
    e2e::assert_quiescent(net);
    e2e::sim_net_deinit(net);
    e2e::assert_all_node_heaps_clean(net);
    e2e::assert_no_live_messages();
}

// ---------------------------------------------------------------------------
// Test 5: Substitutions are correct for pinned topics (pin suffix stripped).
// ---------------------------------------------------------------------------
void test_pinned_topic_substitutions_correct()
{
    constexpr std::uint32_t pub_id = 5020U;

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xA105)));

    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/pin/subst/alpha#100"));
    TEST_ASSERT_NOT_NULL(pub);

    arrival_capture_t  capture{};
    cy_future_t* const sub = make_pattern_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "e2e/pin/subst/*", capture);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    e2e::set_now(net, now);
    publish_best_effort(pub, pub_id, 1U, now);
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
    now += 10'000;
    e2e::drive_for(net, now, delivery_time, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_FALSE(capture.samples.empty());

    // Look up the topic on the subscriber node and verify substitutions.
    const std::uint64_t     hash  = capture.samples.front().topic_hash;
    const cy_topic_t* const topic = cy_topic_find_by_hash(e2e::sim_net_cy(net, e2e::sim_node_b), hash);
    TEST_ASSERT_NOT_NULL(topic);

    const cy_substitution_set_t subs_set = cy_subscriber_substitutions(sub, topic);
    TEST_ASSERT_EQUAL_size_t(1U, subs_set.count);
    TEST_ASSERT_NOT_NULL(subs_set.substitutions);
    TEST_ASSERT_EQUAL_size_t(0U, subs_set.substitutions[0].ordinal);
    // The substitution must be "alpha" — the pin suffix is stripped from the stored name.
    TEST_ASSERT_EQUAL_size_t(5U, subs_set.substitutions[0].str.len);
    TEST_ASSERT_EQUAL_STRING_LEN("alpha", subs_set.substitutions[0].str.str, 5U);

    e2e::cleanup_case(net, now, {}, { sub }, { pub }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test 6: Multiple patterns selectively match pinned and unpinned topics.
// ---------------------------------------------------------------------------
void test_multiple_patterns_selective_match_with_pinning()
{
    constexpr std::uint32_t pub_id_a = 5030U;
    constexpr std::uint32_t pub_id_b = 5031U;

    constexpr std::size_t publisher_node = 0U;
    constexpr std::size_t subscriber_a   = 1U;
    constexpr std::size_t subscriber_b   = 2U;

    e2e::sim_net_config_t cfg{};
    cfg.node_count       = 3U;
    cfg.random_seed_base = UINT64_C(0xA106);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    // Publisher node advertises one pinned and one unpinned topic under different prefixes.
    cy_publisher_t* const pub_a = cy_advertise(e2e::sim_net_cy(net, publisher_node), cy_str("e2e/pin/sel/a/x#600"));
    cy_publisher_t* const pub_b = cy_advertise(e2e::sim_net_cy(net, publisher_node), cy_str("e2e/pin/sel/b/y"));
    TEST_ASSERT_NOT_NULL(pub_a);
    TEST_ASSERT_NOT_NULL(pub_b);

    // Each subscriber node uses a different pattern that should match only one topic.
    arrival_capture_t  capture_a{};
    arrival_capture_t  capture_b{};
    cy_future_t* const sub_a = make_pattern_sub(e2e::sim_net_cy(net, subscriber_a), "e2e/pin/sel/a/>", capture_a);
    cy_future_t* const sub_b = make_pattern_sub(e2e::sim_net_cy(net, subscriber_b), "e2e/pin/sel/b/*", capture_b);

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, converge_time, step_us);

    for (std::uint64_t seq = 1U; seq <= 16U; seq++) {
        e2e::set_now_all(net, now);
        publish_best_effort(pub_a, pub_id_a, seq, now);
        publish_best_effort(pub_b, pub_id_b, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round_all(net, now));
        now += 10'000;
    }
    e2e::drive_for_all(net, now, delivery_time, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture_a.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, capture_b.malformed);

    // Pattern "e2e/pin/sel/a/>" must match only the pinned topic.
    TEST_ASSERT_TRUE(count_by_publisher(capture_a, pub_id_a) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(capture_a, pub_id_b));

    // Pattern "e2e/pin/sel/b/*" must match only the unpinned topic.
    TEST_ASSERT_TRUE(count_by_publisher(capture_b, pub_id_b) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(capture_b, pub_id_a));

    cy_future_destroy(sub_a);
    cy_future_destroy(sub_b);
    e2e::drive_for_all(net, now, 100'000, step_us);
    cy_unadvertise(pub_a);
    cy_unadvertise(pub_b);
    e2e::drive_for_all(net, now, 100'000, step_us);
    e2e::drain_queue_all(net, now, step_us, 100'000U);
    e2e::assert_quiescent(net);
    e2e::sim_net_deinit(net);
    e2e::assert_all_node_heaps_clean(net);
    e2e::assert_no_live_messages();
}

// ---------------------------------------------------------------------------
// Test 7: Implicit topic from gossip inherits remote pinned evictions.
// Node A advertises "data/sensor#200". Node B subscribes to pattern "data/>".
// After gossip rounds, B discovers A's pinned topic and creates an implicit
// topic. The implicit topic on B picks up the pinned subject-ID from gossip,
// and publishing from A delivers to B's pattern subscriber.
// ---------------------------------------------------------------------------
void test_implicit_topic_from_gossip_inherits_remote_evictions()
{
    constexpr std::uint32_t pub_id = 5040U;

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xA107)));

    // Node A: advertise on "data/sensor#200" (pinned to subject-ID 200).
    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("data/sensor#200"));
    TEST_ASSERT_NOT_NULL(pub);

    // Node B: subscribe to pattern "data/>" to match the pinned topic.
    arrival_capture_t  capture{};
    cy_future_t* const sub = make_pattern_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "data/>", capture);

    // Drive gossip rounds so B discovers A's pinned topic.
    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    // Verify B creates an implicit topic for "data/sensor".
    const cy_topic_t* const implicit_topic =
      cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("data/sensor"));
    TEST_ASSERT_NOT_NULL(implicit_topic);

    // The implicit topic on B must use the same topic hash as A's topic.
    const std::uint64_t hash_a = cy_topic_hash(cy_publisher_topic(pub));
    TEST_ASSERT_EQUAL_UINT64(hash_a, cy_topic_hash(implicit_topic));

    // Publish from A and verify delivery to B's pattern subscriber.
    for (std::uint64_t seq = 1U; seq <= 16U; seq++) {
        e2e::set_now(net, now);
        publish_best_effort(pub, pub_id, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture, pub_id) > 0U);

    // Verify the on-wire subject-ID is 200, proving B's implicit topic inherited the pinned evictions.
    const auto&                  caps = e2e::sim_net_captures(net);
    std::optional<std::uint32_t> observed_sid;
    for (std::size_t i = caps.size(); i > 0U; i--) {
        const e2e::frame_capture_t& cap = caps.at(i - 1U);
        if (cap.frame.has_topic_hash && (cap.frame.topic_hash == hash_a) && (cap.frame.header_type <= 1U)) {
            observed_sid = cap.frame.subject_id;
            break;
        }
    }
    TEST_ASSERT_TRUE(observed_sid.has_value());
    TEST_ASSERT_EQUAL_UINT32(200U, *observed_sid);

    e2e::cleanup_case(net, now, {}, { sub }, { pub }, step_us, 100'000, 100'000U);
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
    RUN_TEST(test_pinned_topic_matches_chevron_pattern);
    RUN_TEST(test_pinned_topic_matches_star_pattern);
    RUN_TEST(test_mixed_pinned_unpinned_all_match_same_pattern);
    RUN_TEST(test_multinode_cross_pinned_pattern_delivery);
    RUN_TEST(test_pinned_topic_substitutions_correct);
    RUN_TEST(test_multiple_patterns_selective_match_with_pinning);
    RUN_TEST(test_implicit_topic_from_gossip_inherits_remote_evictions);
    return UNITY_END();
}
