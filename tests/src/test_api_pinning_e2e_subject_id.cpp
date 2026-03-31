// Verify pinning subject-ID assignment, range boundaries, identity, and auto-allocation isolation.
//
// Contracts under test:
//  - A pinned topic has the desired subject-ID encoded as decimal after '#'.
//  - Pinned subject-IDs are in [0, 8191] (0x1FFF).
//  - This range is never used for automatically allocated topics.
//  - Pinning does not affect topic identity; only the name before '#' matters.
//  - Prefixed pinned topics with different names are distinct even if they share a subject-ID.

#include <cy_platform.h>
#include <rapidhash.h>
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
#include <vector>

namespace {

constexpr cy_us_t step_us          = 1'000;
constexpr cy_us_t publish_deadline = 200'000;
constexpr cy_us_t converge_time    = 800'000;
constexpr cy_us_t delivery_time    = 400'000;

using e2e::arrival_capture_t;
using e2e::count_by_publisher;
using e2e::on_arrival_capture;

void publish_one(cy_publisher_t* const pub,
                 const std::uint32_t   publisher_id,
                 const std::uint64_t   seq,
                 const cy_us_t         now)
{
    const auto       payload = e2e::app_payload_pack(publisher_id, seq);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, now + publish_deadline, msg));
}

// Find the last observed subject-ID for a given topic hash among message frames (header types 0 and 1).
std::optional<std::uint32_t> last_subject_id_for_hash(const std::vector<e2e::frame_capture_t>& captures,
                                                      const std::uint64_t                      topic_hash)
{
    for (std::size_t i = captures.size(); i > 0U; i--) {
        const e2e::frame_capture_t& cap = captures.at(i - 1U);
        if (cap.frame.has_topic_hash && (cap.frame.topic_hash == topic_hash) && (cap.frame.header_type <= 1U)) {
            return cap.frame.subject_id;
        }
    }
    return std::nullopt;
}

cy_future_t* make_sub(cy_t* const cy, const char* const name, arrival_capture_t& capture)
{
    cy_future_t* const sub = cy_subscribe(cy, cy_str(name), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &capture;
    cy_future_context_set(sub, ctx);
    cy_future_callback_set(sub, on_arrival_capture);
    return sub;
}

// ---------------------------------------------------------------------------
// Test: Pinned topic gets the exact subject-ID encoded in its name.
// ---------------------------------------------------------------------------
void test_pinned_subject_id_matches_decimal_suffix()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB001)));

    // Advertise on node A, subscribe on node B so the message is actually sent on the wire.
    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/basic#1234"));
    TEST_ASSERT_NOT_NULL(pub);
    arrival_capture_t  capture{};
    cy_future_t* const sub = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "e2e/sid/basic", capture);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    e2e::set_now(net, now);
    publish_one(pub, 6001U, 1U, now);
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
    now += 10'000;
    e2e::drive_for(net, now, delivery_time, step_us);

    const cy_topic_t* const topic = cy_publisher_topic(pub);
    TEST_ASSERT_NOT_NULL(topic);
    const std::uint64_t hash = cy_topic_hash(topic);

    const auto sid = last_subject_id_for_hash(e2e::sim_net_captures(net), hash);
    TEST_ASSERT_TRUE(sid.has_value());
    TEST_ASSERT_EQUAL_UINT32(1234U, *sid);

    // Verify delivery worked.
    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture, 6001U) > 0U);

    e2e::cleanup_case(net, now, {}, { sub }, { pub }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: Pin boundary values: 0, 1, 8191 are all valid pinned subject-IDs.
// ---------------------------------------------------------------------------
void test_pinned_subject_id_boundary_values()
{
    e2e::sim_net_config_t cfg{};
    cfg.node_count       = 2U;
    cfg.random_seed_base = UINT64_C(0xB002);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    // Three pinned topics at the boundary values of the pinned range [0, 8191].
    cy_publisher_t* const pub_min = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/bound/min#0"));
    cy_publisher_t* const pub_one = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/bound/one#1"));
    cy_publisher_t* const pub_max =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/bound/max#8191"));
    TEST_ASSERT_NOT_NULL(pub_min);
    TEST_ASSERT_NOT_NULL(pub_one);
    TEST_ASSERT_NOT_NULL(pub_max);

    arrival_capture_t  capture_min{};
    arrival_capture_t  capture_one{};
    arrival_capture_t  capture_max{};
    cy_future_t* const sub_min = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "e2e/sid/bound/min", capture_min);
    cy_future_t* const sub_one = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "e2e/sid/bound/one", capture_one);
    cy_future_t* const sub_max = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "e2e/sid/bound/max", capture_max);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    e2e::set_now(net, now);
    publish_one(pub_min, 6010U, 1U, now);
    publish_one(pub_one, 6011U, 1U, now);
    publish_one(pub_max, 6012U, 1U, now);
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
    now += 10'000;
    e2e::drive_for(net, now, delivery_time, step_us);

    const auto& caps = e2e::sim_net_captures(net);

    const auto sid_min = last_subject_id_for_hash(caps, cy_topic_hash(cy_publisher_topic(pub_min)));
    const auto sid_one = last_subject_id_for_hash(caps, cy_topic_hash(cy_publisher_topic(pub_one)));
    const auto sid_max = last_subject_id_for_hash(caps, cy_topic_hash(cy_publisher_topic(pub_max)));

    TEST_ASSERT_TRUE(sid_min.has_value());
    TEST_ASSERT_TRUE(sid_one.has_value());
    TEST_ASSERT_TRUE(sid_max.has_value());

    TEST_ASSERT_EQUAL_UINT32(0x0000U, *sid_min);
    TEST_ASSERT_EQUAL_UINT32(0x0001U, *sid_one);
    TEST_ASSERT_EQUAL_UINT32(0x1FFFU, *sid_max);

    // All three topics should deliver successfully.
    TEST_ASSERT_TRUE(count_by_publisher(capture_min, 6010U) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(capture_one, 6011U) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(capture_max, 6012U) > 0U);

    e2e::cleanup_case(
      net, now, {}, { sub_min, sub_one, sub_max }, { pub_min, pub_one, pub_max }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: Auto-allocated topics never use subject-IDs in the pinned range [0, 8191].
// ---------------------------------------------------------------------------
void test_auto_allocated_never_in_pinned_range()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB003)));

    // Create several unpinned topics with diverse names.
    static constexpr std::array<const char*, 6> topic_names = {
        "e2e/sid/auto/alpha", "e2e/sid/auto/beta",    "e2e/sid/auto/gamma",
        "e2e/sid/auto/delta", "e2e/sid/auto/epsilon", "e2e/sid/auto/zeta",
    };

    std::array<cy_publisher_t*, 6>   pubs{};
    std::array<cy_future_t*, 6>      subs{};
    std::array<arrival_capture_t, 6> captures{};

    for (std::size_t i = 0U; i < topic_names.size(); i++) {
        pubs.at(i) = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(topic_names.at(i)));
        TEST_ASSERT_NOT_NULL(pubs.at(i));
        subs.at(i) = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), topic_names.at(i), captures.at(i));
    }

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    e2e::set_now(net, now);
    for (std::size_t i = 0U; i < topic_names.size(); i++) {
        publish_one(pubs.at(i), static_cast<std::uint32_t>(6020U + i), 1U, now);
    }
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
    now += 10'000;
    e2e::drive_for(net, now, delivery_time, step_us);

    const auto& caps = e2e::sim_net_captures(net);
    for (std::size_t i = 0U; i < topic_names.size(); i++) {
        const std::uint64_t hash = cy_topic_hash(cy_publisher_topic(pubs.at(i)));
        const auto          sid  = last_subject_id_for_hash(caps, hash);
        TEST_ASSERT_TRUE(sid.has_value());
        // Auto-allocated subject-IDs must be above the pinned range.
        TEST_ASSERT_TRUE(*sid > CY_SUBJECT_ID_PINNED_MAX);
    }

    const std::vector<cy_future_t*>    sub_vec(subs.begin(), subs.end());
    const std::vector<cy_publisher_t*> pub_vec(pubs.begin(), pubs.end());
    e2e::cleanup_case(net, now, {}, sub_vec, pub_vec, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: Pinning does not affect topic identity.
// 'foo/bar#1234' and 'foo/bar' have the same topic hash.
// The stored name is 'foo/bar' (the part before '#').
// ---------------------------------------------------------------------------
void test_pinning_does_not_affect_identity()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB004)));

    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/ident/topic#100"));
    TEST_ASSERT_NOT_NULL(pub);

    const cy_topic_t* const topic = cy_publisher_topic(pub);
    TEST_ASSERT_NOT_NULL(topic);

    // The topic should be findable by the name WITHOUT the pin suffix.
    const cy_topic_t* const by_name =
      cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/ident/topic"));
    TEST_ASSERT_NOT_NULL(by_name);
    TEST_ASSERT_EQUAL_UINT64(cy_topic_hash(topic), cy_topic_hash(by_name));

    // cy_topic_name() should return the stored name without the pin suffix.
    const cy_str_t name = cy_topic_name(topic);
    TEST_ASSERT_EQUAL_size_t(19U, name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("e2e/sid/ident/topic", name.str, name.len);

    // Attempting to create a second publisher on the SAME logical topic (different pin) should reuse the same topic.
    cy_publisher_t* const pub2 = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/ident/topic#200"));
    TEST_ASSERT_NOT_NULL(pub2);
    TEST_ASSERT_EQUAL_UINT64(cy_topic_hash(topic), cy_topic_hash(cy_publisher_topic(pub2)));

    // Advertising the unpinned version should also reuse the same topic.
    cy_publisher_t* const pub3 = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/ident/topic"));
    TEST_ASSERT_NOT_NULL(pub3);
    TEST_ASSERT_EQUAL_UINT64(cy_topic_hash(topic), cy_topic_hash(cy_publisher_topic(pub3)));

    cy_us_t now = 0;
    e2e::drive_for(net, now, 50'000, step_us);

    cy_unadvertise(pub3);
    cy_unadvertise(pub2);
    e2e::cleanup_case(net, now, {}, {}, { pub }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: Prefixed pinned topics with different names are distinct topics.
// 'pin_a#1234' and 'pin_b#123' have different hashes (rapidhash of the name prefix)
// and different pinned subject-IDs.
// ---------------------------------------------------------------------------
void test_bare_pinned_topics_distinct_identity()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB005)));

    cy_publisher_t* const pub_a = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("pin_a#1234"));
    cy_publisher_t* const pub_b = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("pin_b#123"));
    TEST_ASSERT_NOT_NULL(pub_a);
    TEST_ASSERT_NOT_NULL(pub_b);

    // Different name prefixes produce different hashes (they are distinct topics).
    const std::uint64_t hash_a = cy_topic_hash(cy_publisher_topic(pub_a));
    const std::uint64_t hash_b = cy_topic_hash(cy_publisher_topic(pub_b));
    TEST_ASSERT_TRUE(hash_a != hash_b);

    // Hash is rapidhash of the stored name (the part before '#').
    TEST_ASSERT_EQUAL_UINT64(rapidhash("pin_a", 5U), hash_a);
    TEST_ASSERT_EQUAL_UINT64(rapidhash("pin_b", 5U), hash_b);

    // Subscribe to each topic on node B and verify independent delivery.
    arrival_capture_t  capture_a{};
    arrival_capture_t  capture_b{};
    cy_future_t* const sub_a = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "pin_a", capture_a);
    cy_future_t* const sub_b = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "pin_b", capture_b);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        e2e::set_now(net, now);
        publish_one(pub_a, 6030U, seq, now);
        publish_one(pub_b, 6031U, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, capture_a.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, capture_b.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_a, 6030U) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(capture_b, 6031U) > 0U);

    // Verify subject-IDs match pin values (decimal).
    const auto& caps  = e2e::sim_net_captures(net);
    const auto  sid_a = last_subject_id_for_hash(caps, hash_a);
    const auto  sid_b = last_subject_id_for_hash(caps, hash_b);
    TEST_ASSERT_TRUE(sid_a.has_value());
    TEST_ASSERT_TRUE(sid_b.has_value());
    TEST_ASSERT_EQUAL_UINT32(1234U, *sid_a);
    TEST_ASSERT_EQUAL_UINT32(123U, *sid_b);

    e2e::cleanup_case(net, now, {}, { sub_a, sub_b }, { pub_a, pub_b }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: Two prefixed pins sharing the same subject-ID are different topics.
// 'bare#2748' and 'foo#2748' both pin to subject 2748 but have different hashes.
// ---------------------------------------------------------------------------
void test_bare_pin_differs_from_prefixed_pin()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB006)));

    cy_publisher_t* const pub_bare     = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("bare#2748"));
    cy_publisher_t* const pub_prefixed = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("foo#2748"));
    TEST_ASSERT_NOT_NULL(pub_bare);
    TEST_ASSERT_NOT_NULL(pub_prefixed);

    // Different hashes: rapidhash("bare") vs rapidhash("foo").
    const std::uint64_t hash_bare     = cy_topic_hash(cy_publisher_topic(pub_bare));
    const std::uint64_t hash_prefixed = cy_topic_hash(cy_publisher_topic(pub_prefixed));
    TEST_ASSERT_TRUE(hash_bare != hash_prefixed);
    TEST_ASSERT_EQUAL_UINT64(rapidhash("bare", 4U), hash_bare);
    TEST_ASSERT_EQUAL_UINT64(rapidhash("foo", 3U), hash_prefixed);

    // Despite different hashes, both share subject-ID 2748 (multi-tenant).
    // Subscribe to each and verify independent delivery.
    arrival_capture_t  capture_bare{};
    arrival_capture_t  capture_prefixed{};
    cy_future_t* const sub_bare     = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "bare", capture_bare);
    cy_future_t* const sub_prefixed = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "foo", capture_prefixed);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        e2e::set_now(net, now);
        publish_one(pub_bare, 6040U, seq, now);
        publish_one(pub_prefixed, 6041U, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    // Each subscriber should only receive its own topic's messages.
    TEST_ASSERT_EQUAL_size_t(0U, capture_bare.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, capture_prefixed.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_bare, 6040U) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(capture_bare, 6041U));
    TEST_ASSERT_TRUE(count_by_publisher(capture_prefixed, 6041U) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(capture_prefixed, 6040U));

    e2e::cleanup_case(net, now, {}, { sub_bare, sub_prefixed }, { pub_bare, pub_prefixed }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: Multiple topics sharing a pinned subject-ID are routed correctly.
// 'alpha#100' and 'beta#100' both pin to subject 100, but subscribers for
// each topic receive only the messages from the matching publisher.
// ---------------------------------------------------------------------------
void test_topic_cohabitation_correct_routing()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB007)));

    // Node A publishes on "alpha#100" (pub_id=7001) and "beta#100" (pub_id=7002).
    // Both are pinned to the same subject-ID 100.
    cy_publisher_t* const pub_alpha = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("alpha#100"));
    cy_publisher_t* const pub_beta  = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("beta#100"));
    TEST_ASSERT_NOT_NULL(pub_alpha);
    TEST_ASSERT_NOT_NULL(pub_beta);

    // Verify the two topics are distinct (different hashes) but share the same pinned subject-ID.
    const std::uint64_t hash_alpha = cy_topic_hash(cy_publisher_topic(pub_alpha));
    const std::uint64_t hash_beta  = cy_topic_hash(cy_publisher_topic(pub_beta));
    TEST_ASSERT_TRUE(hash_alpha != hash_beta);

    // Node B subscribes to "alpha" and "beta" separately.
    arrival_capture_t  capture_alpha{};
    arrival_capture_t  capture_beta{};
    cy_future_t* const sub_alpha = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "alpha", capture_alpha);
    cy_future_t* const sub_beta  = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "beta", capture_beta);

    // Drive the network to convergence.
    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    // Publish messages from both topics. Multiple rounds to ensure reliable delivery.
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        e2e::set_now(net, now);
        publish_one(pub_alpha, 7001U, seq, now);
        publish_one(pub_beta, 7002U, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    // Verify: subscriber for "alpha" only gets messages from pub_id=7001.
    TEST_ASSERT_EQUAL_size_t(0U, capture_alpha.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_alpha, 7001U) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(capture_alpha, 7002U));

    // Verify: subscriber for "beta" only gets messages from pub_id=7002.
    TEST_ASSERT_EQUAL_size_t(0U, capture_beta.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_beta, 7002U) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(capture_beta, 7001U));

    // Verify on the wire both topics used subject-ID 100.
    const auto& caps      = e2e::sim_net_captures(net);
    const auto  sid_alpha = last_subject_id_for_hash(caps, hash_alpha);
    const auto  sid_beta  = last_subject_id_for_hash(caps, hash_beta);
    TEST_ASSERT_TRUE(sid_alpha.has_value());
    TEST_ASSERT_TRUE(sid_beta.has_value());
    TEST_ASSERT_EQUAL_UINT32(100U, *sid_alpha);
    TEST_ASSERT_EQUAL_UINT32(100U, *sid_beta);

    e2e::cleanup_case(net, now, {}, { sub_alpha, sub_beta }, { pub_alpha, pub_beta }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: Pinned and auto-allocated topics coexist without interference.
// A pinned topic gets its declared subject-ID (100), and an auto-allocated
// topic gets a subject-ID above CY_SUBJECT_ID_PINNED_MAX. Both deliver
// messages correctly to their respective subscribers.
// ---------------------------------------------------------------------------
void test_pinned_and_auto_coexist()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB008)));

    // Node A: one pinned topic and one auto-allocated topic.
    cy_publisher_t* const pub_pinned =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("pinned/coexist#100"));
    cy_publisher_t* const pub_auto = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("auto/coexist"));
    TEST_ASSERT_NOT_NULL(pub_pinned);
    TEST_ASSERT_NOT_NULL(pub_auto);

    // Node B: subscribe to both.
    arrival_capture_t  capture_pinned{};
    arrival_capture_t  capture_auto{};
    cy_future_t* const sub_pinned = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "pinned/coexist", capture_pinned);
    cy_future_t* const sub_auto   = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "auto/coexist", capture_auto);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    // Publish from both topics.
    constexpr std::uint32_t pinned_pub_id = 7101U;
    constexpr std::uint32_t auto_pub_id   = 7102U;
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        e2e::set_now(net, now);
        publish_one(pub_pinned, pinned_pub_id, seq, now);
        publish_one(pub_auto, auto_pub_id, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    // Verify the pinned topic gets subject-ID 100.
    const auto& caps        = e2e::sim_net_captures(net);
    const auto  hash_pinned = cy_topic_hash(cy_publisher_topic(pub_pinned));
    const auto  hash_auto   = cy_topic_hash(cy_publisher_topic(pub_auto));
    const auto  sid_pinned  = last_subject_id_for_hash(caps, hash_pinned);
    const auto  sid_auto    = last_subject_id_for_hash(caps, hash_auto);

    TEST_ASSERT_TRUE(sid_pinned.has_value());
    TEST_ASSERT_EQUAL_UINT32(100U, *sid_pinned);

    // Verify the auto-allocated topic gets a subject-ID above the pinned range.
    TEST_ASSERT_TRUE(sid_auto.has_value());
    TEST_ASSERT_TRUE(*sid_auto > CY_SUBJECT_ID_PINNED_MAX);

    // Verify both topics deliver messages correctly to their respective subscribers.
    TEST_ASSERT_EQUAL_size_t(0U, capture_pinned.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_pinned, pinned_pub_id) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(capture_pinned, auto_pub_id));

    TEST_ASSERT_EQUAL_size_t(0U, capture_auto.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture_auto, auto_pub_id) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(capture_auto, pinned_pub_id));

    e2e::cleanup_case(net, now, {}, { sub_pinned, sub_auto }, { pub_pinned, pub_auto }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: CAN compatibility pattern from README: "1234#1234".
// The topic name is "1234" and the on-wire subject-ID is 1234.
// ---------------------------------------------------------------------------
void test_can_compat_e2e()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB009)));

    // Node A advertises "1234#1234" (CAN compatibility pattern from README).
    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("1234#1234"));
    TEST_ASSERT_NOT_NULL(pub);

    // Node B subscribes to "1234" (same canonical topic).
    arrival_capture_t  capture{};
    cy_future_t* const sub = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "1234", capture);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    // Publish from A.
    constexpr std::uint32_t pub_id = 6050U;
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        e2e::set_now(net, now);
        publish_one(pub, pub_id, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    // Verify B receives the message.
    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture, pub_id) > 0U);

    // Verify the on-wire subject-ID is 1234.
    const auto& caps = e2e::sim_net_captures(net);
    const auto  hash = cy_topic_hash(cy_publisher_topic(pub));
    const auto  sid  = last_subject_id_for_hash(caps, hash);
    TEST_ASSERT_TRUE(sid.has_value());
    TEST_ASSERT_EQUAL_UINT32(1234U, *sid);

    // Verify the stored topic name is "1234" (without the pin suffix).
    const cy_topic_t* const topic = cy_publisher_topic(pub);
    TEST_ASSERT_NOT_NULL(topic);
    const cy_str_t name = cy_topic_name(topic);
    TEST_ASSERT_EQUAL_size_t(4U, name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("1234", name.str, name.len);

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
    RUN_TEST(test_pinned_subject_id_matches_decimal_suffix);
    RUN_TEST(test_pinned_subject_id_boundary_values);
    RUN_TEST(test_auto_allocated_never_in_pinned_range);
    RUN_TEST(test_pinning_does_not_affect_identity);
    RUN_TEST(test_bare_pinned_topics_distinct_identity);
    RUN_TEST(test_bare_pin_differs_from_prefixed_pin);
    RUN_TEST(test_topic_cohabitation_correct_routing);
    RUN_TEST(test_pinned_and_auto_coexist);
    RUN_TEST(test_can_compat_e2e);
    return UNITY_END();
}
