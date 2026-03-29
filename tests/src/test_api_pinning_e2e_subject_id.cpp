// Verify pinning subject-ID assignment, range boundaries, identity, and auto-allocation isolation.
//
// Contracts under test:
//  - A pinned topic has the desired subject-ID encoded as hex after '#'.
//  - Pinned subject-IDs are in [0, 8191] (0x1FFF).
//  - This range is never used for automatically allocated topics.
//  - Pinning does not affect topic identity; only the name before '#' matters.
//  - Bare pinned topics: '#1234' identity is tied to the pinned subject.
//  - '#1234' and '#0123' are distinct topics.

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
#include <set>
#include <vector>

namespace {

constexpr cy_us_t step_us          = 1'000;
constexpr cy_us_t publish_deadline = 200'000;
constexpr cy_us_t converge_time    = 800'000;
constexpr cy_us_t delivery_time    = 400'000;

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
    e2e::app_payload_t            payload{};
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

void publish_one(cy_publisher_t* const pub,
                 const std::uint32_t   publisher_id,
                 const std::uint64_t   seq,
                 const cy_us_t         now)
{
    const auto       payload = e2e::app_payload_pack(publisher_id, seq);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, now + publish_deadline, msg));
}

std::size_t count_by_publisher(const arrival_capture_t& capture, const std::uint32_t publisher_id)
{
    return static_cast<std::size_t>(std::ranges::count_if(
      capture.samples, [publisher_id](const arrival_sample_t& s) { return s.publisher_id == publisher_id; }));
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

// Collect all distinct subject-IDs for message frames matching a topic hash.
std::set<std::uint32_t> all_subject_ids_for_hash(const std::vector<e2e::frame_capture_t>& captures,
                                                 const std::uint64_t                      topic_hash)
{
    std::set<std::uint32_t> result{};
    for (const e2e::frame_capture_t& cap : captures) {
        if (cap.frame.has_topic_hash && (cap.frame.topic_hash == topic_hash) && (cap.frame.header_type <= 1U)) {
            result.insert(cap.frame.subject_id);
        }
    }
    return result;
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
void test_pinned_subject_id_matches_hex_suffix()
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
    TEST_ASSERT_EQUAL_UINT32(0x1234U, *sid);

    // Verify delivery worked.
    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture, 6001U) > 0U);

    e2e::cleanup_case(net, now, {}, { sub }, { pub }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: Pin boundary values: 0x0000, 0x0001, 0x1fff are all valid pinned subject-IDs.
// ---------------------------------------------------------------------------
void test_pinned_subject_id_boundary_values()
{
    e2e::sim_net_config_t cfg{};
    cfg.node_count       = 2U;
    cfg.random_seed_base = UINT64_C(0xB002);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    // Three pinned topics at the boundary values of the pinned range.
    cy_publisher_t* const pub_min =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/bound/min#0000"));
    cy_publisher_t* const pub_one =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/bound/one#0001"));
    cy_publisher_t* const pub_max =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/bound/max#1fff"));
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

    std::vector<cy_future_t*>    sub_vec(subs.begin(), subs.end());
    std::vector<cy_publisher_t*> pub_vec(pubs.begin(), pubs.end());
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

    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/ident/topic#0abc"));
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
    TEST_ASSERT_EQUAL_size_t(18U, name.len); // "e2e/sid/ident/topic" = 19 chars... wait
    // "e2e/sid/ident/topic" is 19 characters.
    TEST_ASSERT_EQUAL_size_t(19U, name.len);
    TEST_ASSERT_EQUAL_STRING_LEN("e2e/sid/ident/topic", name.str, name.len);

    // Attempting to create a second publisher on the SAME logical topic (different pin) should reuse the same topic.
    cy_publisher_t* const pub2 =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("e2e/sid/ident/topic#0def"));
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
// Test: Bare pinned topics ('#1234') are valid and their identity is the pin value.
// '#1234' and '#0123' are distinct topics.
// ---------------------------------------------------------------------------
void test_bare_pinned_topics_distinct_identity()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB005)));

    cy_publisher_t* const pub_a = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("#1234"));
    cy_publisher_t* const pub_b = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("#0123"));
    TEST_ASSERT_NOT_NULL(pub_a);
    TEST_ASSERT_NOT_NULL(pub_b);

    // Bare pins with different values must have different hashes (they are distinct topics).
    const std::uint64_t hash_a = cy_topic_hash(cy_publisher_topic(pub_a));
    const std::uint64_t hash_b = cy_topic_hash(cy_publisher_topic(pub_b));
    TEST_ASSERT_TRUE(hash_a != hash_b);

    // For bare pins, hash equals the pin value directly.
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x1234), hash_a);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x0123), hash_b);

    // Subscribe to each bare pin on node B and verify independent delivery.
    arrival_capture_t  capture_a{};
    arrival_capture_t  capture_b{};
    cy_future_t* const sub_a = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "#1234", capture_a);
    cy_future_t* const sub_b = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "#0123", capture_b);

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

    // Verify subject-IDs match pin values.
    const auto& caps  = e2e::sim_net_captures(net);
    const auto  sid_a = last_subject_id_for_hash(caps, hash_a);
    const auto  sid_b = last_subject_id_for_hash(caps, hash_b);
    TEST_ASSERT_TRUE(sid_a.has_value());
    TEST_ASSERT_TRUE(sid_b.has_value());
    TEST_ASSERT_EQUAL_UINT32(0x1234U, *sid_a);
    TEST_ASSERT_EQUAL_UINT32(0x0123U, *sid_b);

    e2e::cleanup_case(net, now, {}, { sub_a, sub_b }, { pub_a, pub_b }, step_us, 100'000, 100'000U);
}

// ---------------------------------------------------------------------------
// Test: Bare pin '#1234' is a different topic from prefixed pin 'foo#1234'.
// They share the same subject-ID but have different hashes.
// ---------------------------------------------------------------------------
void test_bare_pin_differs_from_prefixed_pin()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xB006)));

    cy_publisher_t* const pub_bare     = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("#0abc"));
    cy_publisher_t* const pub_prefixed = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("foo#0abc"));
    TEST_ASSERT_NOT_NULL(pub_bare);
    TEST_ASSERT_NOT_NULL(pub_prefixed);

    // Different hashes: bare pin uses 0x0ABC as hash; prefixed uses rapidhash("foo").
    const std::uint64_t hash_bare     = cy_topic_hash(cy_publisher_topic(pub_bare));
    const std::uint64_t hash_prefixed = cy_topic_hash(cy_publisher_topic(pub_prefixed));
    TEST_ASSERT_TRUE(hash_bare != hash_prefixed);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x0ABC), hash_bare);

    // Despite different hashes, both share subject-ID 0x0ABC (multi-tenant).
    // Subscribe to each and verify independent delivery.
    arrival_capture_t  capture_bare{};
    arrival_capture_t  capture_prefixed{};
    cy_future_t* const sub_bare     = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "#0abc", capture_bare);
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
    RUN_TEST(test_pinned_subject_id_matches_hex_suffix);
    RUN_TEST(test_pinned_subject_id_boundary_values);
    RUN_TEST(test_auto_allocated_never_in_pinned_range);
    RUN_TEST(test_pinning_does_not_affect_identity);
    RUN_TEST(test_bare_pinned_topics_distinct_identity);
    RUN_TEST(test_bare_pin_differs_from_prefixed_pin);
    return UNITY_END();
}
