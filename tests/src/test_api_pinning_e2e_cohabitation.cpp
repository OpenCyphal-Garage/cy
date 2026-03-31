// E2E tests for pinned topic cohabitation, explicit CRDT arbitration cases, and gossip name invariants.

#include <cy_platform.h>
#include <rapidhash.h>
#include <unity.h>
#include "e2e_sim_net.hpp"
#include "e2e_scenario_utils.hpp"
#include "e2e_test_utils.hpp"
#include "message.h"
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string>
#include <vector>

namespace {

constexpr cy_us_t      step_us          = 1'000;
constexpr cy_us_t      publish_deadline = 200'000;
constexpr cy_us_t      converge_time    = 2'000'000;
constexpr cy_us_t      delivery_time    = 400'000;
constexpr std::uint8_t header_gossip    = 8U;
constexpr std::size_t  header_bytes     = 24U;

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

std::uint32_t require_last_subject_id_for_hash(const std::vector<e2e::frame_capture_t>& captures,
                                               const std::uint64_t                      topic_hash)
{
    const auto sid = last_subject_id_for_hash(captures, topic_hash);
    TEST_ASSERT_TRUE(sid.has_value());
    return *sid;
}

void assert_remote_only(const arrival_capture_t& capture,
                        const std::uint32_t      expected_publisher_id,
                        const std::uint32_t      unexpected_publisher_id)
{
    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(capture, expected_publisher_id) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(capture, unexpected_publisher_id));
}

void cleanup_all(e2e::sim_net_t&                     net,
                 cy_us_t&                            now,
                 const std::vector<cy_future_t*>&    subs,
                 const std::vector<cy_publisher_t*>& pubs)
{
    for (cy_future_t* const sub : subs) {
        if (sub != nullptr) {
            cy_future_destroy(sub);
        }
    }
    e2e::drive_for_all(net, now, 80'000, step_us);
    for (cy_publisher_t* const pub : pubs) {
        if (pub != nullptr) {
            cy_unadvertise(pub);
        }
    }
    e2e::drive_for_all(net, now, 80'000, step_us);
    e2e::drain_queue_all(net, now, step_us, 80'000U);
    e2e::assert_quiescent(net);
    e2e::sim_net_deinit(net);
    e2e::assert_all_node_heaps_clean(net);
    e2e::assert_no_live_messages();
}

// ---------------------------------------------------------------------------
// Test 1: 3-node cohabitation. Two topics pinned to the same subject-ID,
// published by different nodes, received without misdelivery.
// ---------------------------------------------------------------------------
void test_multinode_cohabitation_no_misdelivery()
{
    e2e::sim_net_config_t cfg{};
    cfg.node_count       = 3U;
    cfg.random_seed_base = UINT64_C(0xC001);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    // Node 0 publishes alpha#100, subscribes to beta.
    cy_publisher_t* const pub_alpha = cy_advertise(e2e::sim_net_cy(net, 0U), cy_str("alpha#100"));
    TEST_ASSERT_NOT_NULL(pub_alpha);
    arrival_capture_t  cap_n0_beta{};
    cy_future_t* const sub_n0_beta = make_sub(e2e::sim_net_cy(net, 0U), "beta", cap_n0_beta);

    // Node 1 publishes beta#100, subscribes to alpha.
    cy_publisher_t* const pub_beta = cy_advertise(e2e::sim_net_cy(net, 1U), cy_str("beta#100"));
    TEST_ASSERT_NOT_NULL(pub_beta);
    arrival_capture_t  cap_n1_alpha{};
    cy_future_t* const sub_n1_alpha = make_sub(e2e::sim_net_cy(net, 1U), "alpha", cap_n1_alpha);

    // Node 2 subscribes to both.
    arrival_capture_t  cap_n2_alpha{};
    arrival_capture_t  cap_n2_beta{};
    cy_future_t* const sub_n2_alpha = make_sub(e2e::sim_net_cy(net, 2U), "alpha", cap_n2_alpha);
    cy_future_t* const sub_n2_beta  = make_sub(e2e::sim_net_cy(net, 2U), "beta", cap_n2_beta);

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, converge_time, step_us);

    constexpr std::uint32_t alpha_pub_id = 8001U;
    constexpr std::uint32_t beta_pub_id  = 8002U;
    for (std::uint64_t seq = 1U; seq <= 16U; seq++) {
        e2e::set_now_all(net, now);
        publish_one(pub_alpha, alpha_pub_id, seq, now);
        publish_one(pub_beta, beta_pub_id, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round_all(net, now));
        now += 10'000;
    }
    e2e::drive_for_all(net, now, delivery_time, step_us);

    // Node 0's beta subscriber: only beta messages.
    TEST_ASSERT_EQUAL_size_t(0U, cap_n0_beta.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(cap_n0_beta, beta_pub_id) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(cap_n0_beta, alpha_pub_id));

    // Node 1's alpha subscriber: only alpha messages.
    TEST_ASSERT_EQUAL_size_t(0U, cap_n1_alpha.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(cap_n1_alpha, alpha_pub_id) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(cap_n1_alpha, beta_pub_id));

    // Node 2's alpha subscriber: only alpha messages.
    TEST_ASSERT_EQUAL_size_t(0U, cap_n2_alpha.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(cap_n2_alpha, alpha_pub_id) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(cap_n2_alpha, beta_pub_id));

    // Node 2's beta subscriber: only beta messages.
    TEST_ASSERT_EQUAL_size_t(0U, cap_n2_beta.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(cap_n2_beta, beta_pub_id) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(cap_n2_beta, alpha_pub_id));

    // On-wire subject-ID for both topics is 100.
    const auto& caps      = e2e::sim_net_captures(net);
    const auto  hash_a    = cy_topic_hash(cy_publisher_topic(pub_alpha));
    const auto  hash_b    = cy_topic_hash(cy_publisher_topic(pub_beta));
    const auto  sid_alpha = last_subject_id_for_hash(caps, hash_a);
    const auto  sid_beta  = last_subject_id_for_hash(caps, hash_b);
    TEST_ASSERT_TRUE(sid_alpha.has_value());
    TEST_ASSERT_TRUE(sid_beta.has_value());
    TEST_ASSERT_EQUAL_UINT32(100U, *sid_alpha);
    TEST_ASSERT_EQUAL_UINT32(100U, *sid_beta);

    cleanup_all(net, now, { sub_n0_beta, sub_n1_alpha, sub_n2_alpha, sub_n2_beta }, { pub_alpha, pub_beta });
}

// ---------------------------------------------------------------------------
// Test 2: 3-node cohabitation with three topics all sharing one pin.
// Each node publishes one topic and subscribes to all three.
// ---------------------------------------------------------------------------
void test_multinode_cohabitation_with_three_topics()
{
    e2e::sim_net_config_t cfg{};
    cfg.node_count       = 3U;
    cfg.random_seed_base = UINT64_C(0xC002);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    constexpr std::array<const char*, 3>   topic_names = { "topic_x#200", "topic_y#200", "topic_z#200" };
    constexpr std::array<const char*, 3>   sub_names   = { "topic_x", "topic_y", "topic_z" };
    constexpr std::array<std::uint32_t, 3> pub_ids     = { 9001U, 9002U, 9003U };

    // Each node publishes one topic.
    std::array<cy_publisher_t*, 3> pubs{};
    for (std::size_t i = 0U; i < 3U; i++) {
        pubs.at(i) = cy_advertise(e2e::sim_net_cy(net, i), cy_str(topic_names.at(i)));
        TEST_ASSERT_NOT_NULL(pubs.at(i));
    }

    // Each node subscribes to the two topics it does NOT publish.
    // Node i publishes topic i, subscribes to the other two.
    // caps[node][j] = capture for the j-th subscription of that node, where j maps to the other topics.
    std::array<std::array<arrival_capture_t, 2>, 3> caps{};
    std::vector<cy_future_t*>                       all_subs;
    for (std::size_t node = 0U; node < 3U; node++) {
        std::size_t sub_idx = 0U;
        for (std::size_t topic = 0U; topic < 3U; topic++) {
            if (topic == node) {
                continue; // skip own topic -- sim_net doesn't loopback
            }
            cy_future_t* const sub =
              make_sub(e2e::sim_net_cy(net, node), sub_names.at(topic), caps.at(node).at(sub_idx));
            all_subs.push_back(sub);
            sub_idx++;
        }
    }

    cy_us_t now = 0;
    e2e::drive_for_all(net, now, converge_time, step_us);

    for (std::uint64_t seq = 1U; seq <= 12U; seq++) {
        e2e::set_now_all(net, now);
        for (std::size_t i = 0U; i < 3U; i++) {
            publish_one(pubs.at(i), pub_ids.at(i), seq, now);
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round_all(net, now));
        now += 10'000;
    }
    e2e::drive_for_all(net, now, delivery_time, step_us);

    // Each subscription receives only the correct topic's publisher.
    for (std::size_t node = 0U; node < 3U; node++) {
        std::size_t sub_idx = 0U;
        for (std::size_t topic = 0U; topic < 3U; topic++) {
            if (topic == node) {
                continue;
            }
            const arrival_capture_t& cap = caps.at(node).at(sub_idx);
            TEST_ASSERT_EQUAL_size_t(0U, cap.malformed);
            // Must receive messages from the publisher of this topic.
            TEST_ASSERT_TRUE(count_by_publisher(cap, pub_ids.at(topic)) > 0U);
            // Must NOT receive messages from the other two publishers.
            for (std::size_t other = 0U; other < 3U; other++) {
                if (other != topic) {
                    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(cap, pub_ids.at(other)));
                }
            }
            sub_idx++;
        }
    }

    // On-wire subject-ID for all three topics is 200.
    const auto& frame_caps = e2e::sim_net_captures(net);
    for (std::size_t i = 0U; i < 3U; i++) {
        const auto hash = cy_topic_hash(cy_publisher_topic(pubs.at(i)));
        const auto sid  = last_subject_id_for_hash(frame_caps, hash);
        TEST_ASSERT_TRUE(sid.has_value());
        TEST_ASSERT_EQUAL_UINT32(200U, *sid);
    }

    const std::vector<cy_publisher_t*> pub_vec(pubs.begin(), pubs.end());
    cleanup_all(net, now, all_subs, pub_vec);
}

// ---------------------------------------------------------------------------
// Test 3: An older unpinned topic beats a newer conflicting pinned topic.
// ---------------------------------------------------------------------------
void test_older_unpinned_beats_newer_pinned()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xC003)));

    cy_publisher_t* const pub_old = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("arb/older/unpinned"));
    TEST_ASSERT_NOT_NULL(pub_old);

    cy_us_t now = 0;
    e2e::drive_for(net, now, 4'000'000, step_us);

    cy_publisher_t* const pub_new =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("arb/older/unpinned#321"));
    TEST_ASSERT_NOT_NULL(pub_new);
    TEST_ASSERT_EQUAL_UINT64(cy_topic_hash(cy_publisher_topic(pub_old)), cy_topic_hash(cy_publisher_topic(pub_new)));

    arrival_capture_t  cap_a{};
    arrival_capture_t  cap_b{};
    cy_future_t* const sub_a = make_sub(e2e::sim_net_cy(net, e2e::sim_node_a), "arb/older/unpinned", cap_a);
    cy_future_t* const sub_b = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "arb/older/unpinned", cap_b);

    e2e::drive_for(net, now, converge_time, step_us);

    constexpr std::uint32_t pub_id_old = 5501U;
    constexpr std::uint32_t pub_id_new = 5502U;
    for (std::uint64_t seq = 1U; seq <= 12U; seq++) {
        e2e::set_now(net, now);
        publish_one(pub_old, pub_id_old, seq, now);
        publish_one(pub_new, pub_id_new, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    assert_remote_only(cap_a, pub_id_new, pub_id_old);
    assert_remote_only(cap_b, pub_id_old, pub_id_new);

    const auto& frame_caps = e2e::sim_net_captures(net);
    const auto  topic_hash = cy_topic_hash(cy_publisher_topic(pub_old));
    const auto  sid        = require_last_subject_id_for_hash(frame_caps, topic_hash);
    TEST_ASSERT_TRUE(sid > CY_SUBJECT_ID_PINNED_MAX);

    cleanup_all(net, now, { sub_a, sub_b }, { pub_old, pub_new });
}

// ---------------------------------------------------------------------------
// Test 4: Equal-log-age conflicts are resolved by evictions, so pinned beats
// unpinned on the tie.
// ---------------------------------------------------------------------------
void test_equal_lage_pinned_beats_unpinned_by_evictions()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xC004)));

    cy_publisher_t* const pub_unpinned =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("arb/equal/pin-tie"));
    cy_publisher_t* const pub_pinned =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("arb/equal/pin-tie#123"));
    TEST_ASSERT_NOT_NULL(pub_unpinned);
    TEST_ASSERT_NOT_NULL(pub_pinned);
    TEST_ASSERT_EQUAL_UINT64(cy_topic_hash(cy_publisher_topic(pub_unpinned)),
                             cy_topic_hash(cy_publisher_topic(pub_pinned)));

    arrival_capture_t  cap_a{};
    arrival_capture_t  cap_b{};
    cy_future_t* const sub_a = make_sub(e2e::sim_net_cy(net, e2e::sim_node_a), "arb/equal/pin-tie", cap_a);
    cy_future_t* const sub_b = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "arb/equal/pin-tie", cap_b);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    constexpr std::uint32_t pub_id_unpinned = 5601U;
    constexpr std::uint32_t pub_id_pinned   = 5602U;
    for (std::uint64_t seq = 1U; seq <= 12U; seq++) {
        e2e::set_now(net, now);
        publish_one(pub_unpinned, pub_id_unpinned, seq, now);
        publish_one(pub_pinned, pub_id_pinned, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    assert_remote_only(cap_a, pub_id_pinned, pub_id_unpinned);
    assert_remote_only(cap_b, pub_id_unpinned, pub_id_pinned);

    const auto& frame_caps = e2e::sim_net_captures(net);
    const auto  topic_hash = cy_topic_hash(cy_publisher_topic(pub_unpinned));
    TEST_ASSERT_EQUAL_UINT32(123U, require_last_subject_id_for_hash(frame_caps, topic_hash));

    cleanup_all(net, now, { sub_a, sub_b }, { pub_unpinned, pub_pinned });
}

// ---------------------------------------------------------------------------
// Test 5: A late local pin request attaches to the existing topic instance
// without rewriting its allocation.
// ---------------------------------------------------------------------------
void test_late_local_pin_request_does_not_rewrite_existing_topic()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xC005)));

    cy_publisher_t* const pub_plain = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("arb/local/late-pin"));
    TEST_ASSERT_NOT_NULL(pub_plain);

    arrival_capture_t  cap_b{};
    cy_future_t* const sub_b = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "arb/local/late-pin", cap_b);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    cy_publisher_t* const pub_late_pin =
      cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("arb/local/late-pin#777"));
    TEST_ASSERT_NOT_NULL(pub_late_pin);
    TEST_ASSERT_TRUE(cy_publisher_topic(pub_plain) == cy_publisher_topic(pub_late_pin));
    TEST_ASSERT_EQUAL_size_t(0U, e2e::sim_net_async_errors(net).size());

    constexpr std::uint32_t pub_id_plain = 5701U;
    constexpr std::uint32_t pub_id_late  = 5702U;
    for (std::uint64_t seq = 1U; seq <= 12U; seq++) {
        e2e::set_now(net, now);
        publish_one(pub_plain, pub_id_plain, seq, now);
        publish_one(pub_late_pin, pub_id_late, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, cap_b.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(cap_b, pub_id_plain) > 0U);
    TEST_ASSERT_TRUE(count_by_publisher(cap_b, pub_id_late) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, e2e::sim_net_async_errors(net).size());

    const auto& frame_caps = e2e::sim_net_captures(net);
    const auto  topic_hash = cy_topic_hash(cy_publisher_topic(pub_plain));
    const auto  sid        = require_last_subject_id_for_hash(frame_caps, topic_hash);
    TEST_ASSERT_TRUE(sid > CY_SUBJECT_ID_PINNED_MAX);

    cleanup_all(net, now, { sub_b }, { pub_plain, pub_late_pin });
}

// ---------------------------------------------------------------------------
// Test 6: Cohabitation with reliable delivery.
// Two topics pinned to the same subject-ID, published reliably.
// Reliable futures must resolve with CY_OK and no cross-delivery.
// ---------------------------------------------------------------------------
void test_cohabitation_reliable_delivery()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xC005)));

    // Node A publishes reliably on alpha#500 and beta#500.
    cy_publisher_t* const pub_alpha = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("alpha#500"));
    cy_publisher_t* const pub_beta  = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("beta#500"));
    TEST_ASSERT_NOT_NULL(pub_alpha);
    TEST_ASSERT_NOT_NULL(pub_beta);

    // Node B subscribes to alpha and beta.
    arrival_capture_t  cap_alpha{};
    arrival_capture_t  cap_beta{};
    cy_future_t* const sub_alpha = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "alpha", cap_alpha);
    cy_future_t* const sub_beta  = make_sub(e2e::sim_net_cy(net, e2e::sim_node_b), "beta", cap_beta);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    // Publish reliably and collect futures.
    constexpr std::uint32_t   alpha_pub_id = 8501U;
    constexpr std::uint32_t   beta_pub_id  = 8502U;
    std::vector<cy_future_t*> futures;
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        e2e::set_now(net, now);

        const auto         payload_a = e2e::app_payload_pack(alpha_pub_id, seq);
        const cy_bytes_t   msg_a     = { .size = payload_a.size(), .data = payload_a.data(), .next = nullptr };
        cy_future_t* const fut_a     = cy_publish_reliable(pub_alpha, now + publish_deadline, msg_a);
        TEST_ASSERT_NOT_NULL(fut_a);
        futures.push_back(fut_a);

        const auto         payload_b = e2e::app_payload_pack(beta_pub_id, seq);
        const cy_bytes_t   msg_b     = { .size = payload_b.size(), .data = payload_b.data(), .next = nullptr };
        cy_future_t* const fut_b     = cy_publish_reliable(pub_beta, now + publish_deadline, msg_b);
        TEST_ASSERT_NOT_NULL(fut_b);
        futures.push_back(fut_b);

        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }

    // Drive rounds until all reliable futures resolve.
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, futures, delivery_time, step_us));
    e2e::drive_for(net, now, 80'000, step_us);

    // All reliable futures must resolve with CY_OK.
    for (const cy_future_t* const fut : futures) {
        TEST_ASSERT_TRUE(cy_future_done(fut));
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(fut));
    }

    // No cross-delivery: alpha subscriber gets only alpha messages.
    TEST_ASSERT_EQUAL_size_t(0U, cap_alpha.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(cap_alpha, alpha_pub_id) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(cap_alpha, beta_pub_id));

    // No cross-delivery: beta subscriber gets only beta messages.
    TEST_ASSERT_EQUAL_size_t(0U, cap_beta.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(cap_beta, beta_pub_id) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(cap_beta, alpha_pub_id));

    // Verify payload content: alpha subscriber received the correct publisher_id.
    for (const auto& s : cap_alpha.samples) {
        TEST_ASSERT_EQUAL_UINT32(alpha_pub_id, s.publisher_id);
    }
    for (const auto& s : cap_beta.samples) {
        TEST_ASSERT_EQUAL_UINT32(beta_pub_id, s.publisher_id);
    }

    // On-wire subject-ID for both topics is 500.
    const auto& caps      = e2e::sim_net_captures(net);
    const auto  hash_a    = cy_topic_hash(cy_publisher_topic(pub_alpha));
    const auto  hash_b    = cy_topic_hash(cy_publisher_topic(pub_beta));
    const auto  sid_alpha = last_subject_id_for_hash(caps, hash_a);
    const auto  sid_beta  = last_subject_id_for_hash(caps, hash_b);
    TEST_ASSERT_TRUE(sid_alpha.has_value());
    TEST_ASSERT_TRUE(sid_beta.has_value());
    TEST_ASSERT_EQUAL_UINT32(500U, *sid_alpha);
    TEST_ASSERT_EQUAL_UINT32(500U, *sid_beta);

    e2e::destroy_futures(futures);
    cleanup_all(net, now, { sub_alpha, sub_beta }, { pub_alpha, pub_beta });
}

// ---------------------------------------------------------------------------
// Test 7: Cohabitation with ordered subscribers.
// Two topics pinned to the same subject-ID, received via cy_subscribe_ordered.
// Messages must arrive in-order per-topic and no cross-contamination.
// ---------------------------------------------------------------------------
void test_cohabitation_ordered_subscriber()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(
      CY_OK, e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), UINT64_C(0xC006)));

    // Node A publishes on ord/x#600 and ord/y#600.
    cy_publisher_t* const pub_x = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("ord/x#600"));
    cy_publisher_t* const pub_y = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str("ord/y#600"));
    TEST_ASSERT_NOT_NULL(pub_x);
    TEST_ASSERT_NOT_NULL(pub_y);

    // Node B subscribes to both using ordered subscribers with a reordering window.
    constexpr cy_us_t reordering_window = 50'000;
    arrival_capture_t cap_x{};
    arrival_capture_t cap_y{};

    cy_future_t* const sub_x =
      cy_subscribe_ordered(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("ord/x"), 64U, reordering_window);
    TEST_ASSERT_NOT_NULL(sub_x);
    {
        cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
        ctx.ptr[0]            = &cap_x;
        cy_future_context_set(sub_x, ctx);
        cy_future_callback_set(sub_x, on_arrival_capture);
    }

    cy_future_t* const sub_y =
      cy_subscribe_ordered(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str("ord/y"), 64U, reordering_window);
    TEST_ASSERT_NOT_NULL(sub_y);
    {
        cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
        ctx.ptr[0]            = &cap_y;
        cy_future_context_set(sub_y, ctx);
        cy_future_callback_set(sub_y, on_arrival_capture);
    }

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    // Publish several messages on each topic with distinct sequences.
    constexpr std::uint32_t pub_id_x = 8601U;
    constexpr std::uint32_t pub_id_y = 8602U;
    for (std::uint64_t seq = 1U; seq <= 16U; seq++) {
        e2e::set_now(net, now);
        publish_one(pub_x, pub_id_x, seq, now);
        publish_one(pub_y, pub_id_y, seq, now);
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += 10'000;
    }
    e2e::drive_for(net, now, delivery_time, step_us);

    // Verify no malformed messages and no cross-contamination.
    TEST_ASSERT_EQUAL_size_t(0U, cap_x.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cap_y.malformed);
    TEST_ASSERT_TRUE(count_by_publisher(cap_x, pub_id_x) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(cap_x, pub_id_y));
    TEST_ASSERT_TRUE(count_by_publisher(cap_y, pub_id_y) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, count_by_publisher(cap_y, pub_id_x));

    // Verify messages arrived in-order per-topic (sequence numbers non-decreasing).
    std::uint64_t prev_seq_x = 0U;
    for (const auto& s : cap_x.samples) {
        TEST_ASSERT_TRUE(s.sequence >= prev_seq_x);
        prev_seq_x = s.sequence;
    }
    std::uint64_t prev_seq_y = 0U;
    for (const auto& s : cap_y.samples) {
        TEST_ASSERT_TRUE(s.sequence >= prev_seq_y);
        prev_seq_y = s.sequence;
    }

    // On-wire subject-ID for both topics is 600.
    const auto& caps   = e2e::sim_net_captures(net);
    const auto  hash_x = cy_topic_hash(cy_publisher_topic(pub_x));
    const auto  hash_y = cy_topic_hash(cy_publisher_topic(pub_y));
    const auto  sid_x  = last_subject_id_for_hash(caps, hash_x);
    const auto  sid_y  = last_subject_id_for_hash(caps, hash_y);
    TEST_ASSERT_TRUE(sid_x.has_value());
    TEST_ASSERT_TRUE(sid_y.has_value());
    TEST_ASSERT_EQUAL_UINT32(600U, *sid_x);
    TEST_ASSERT_EQUAL_UINT32(600U, *sid_y);

    cleanup_all(net, now, { sub_x, sub_y }, { pub_x, pub_y });
}

// ---------------------------------------------------------------------------
// Test 8: Every gossip frame has a normalized name (no '#', no '//', no
// leading/trailing '/') and hash == rapidhash(gossiped_name).
// ---------------------------------------------------------------------------
void test_gossip_names_normalized_and_hash_consistent()
{
    e2e::sim_net_config_t cfg{};
    cfg.node_count       = 2U;
    cfg.random_seed_base = UINT64_C(0xC004);

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init_ex(net, cfg));

    // Create topics that exercise normalization and pin stripping.
    cy_publisher_t* const pub_basic  = cy_advertise(e2e::sim_net_cy(net, 0U), cy_str("norm/basic"));
    cy_publisher_t* const pub_slash  = cy_advertise(e2e::sim_net_cy(net, 0U), cy_str("norm/slashy//double"));
    cy_publisher_t* const pub_pinned = cy_advertise(e2e::sim_net_cy(net, 0U), cy_str("norm/pinned#500"));
    TEST_ASSERT_NOT_NULL(pub_basic);
    TEST_ASSERT_NOT_NULL(pub_slash);
    TEST_ASSERT_NOT_NULL(pub_pinned);

    // Subscribe on node 1 so that gossip flows.
    arrival_capture_t  cap_basic{};
    arrival_capture_t  cap_slash{};
    arrival_capture_t  cap_pinned{};
    cy_future_t* const sub_basic  = make_sub(e2e::sim_net_cy(net, 1U), "norm/basic", cap_basic);
    cy_future_t* const sub_slash  = make_sub(e2e::sim_net_cy(net, 1U), "norm/slashy/double", cap_slash);
    cy_future_t* const sub_pinned = make_sub(e2e::sim_net_cy(net, 1U), "norm/pinned", cap_pinned);

    cy_us_t now = 0;
    e2e::drive_for(net, now, converge_time, step_us);

    // Scan all captured frames for gossip invariants.
    const auto& caps             = e2e::sim_net_captures(net);
    std::size_t gossip_count     = 0U;
    std::size_t gossip_with_name = 0U;
    for (const auto& cap : caps) {
        if (cap.frame.header_type != header_gossip) {
            continue;
        }
        gossip_count++;
        if (cap.frame.wire.size() < header_bytes) {
            continue;
        }
        const std::uint8_t name_len = cap.frame.wire.at(header_bytes - 1U);
        if (name_len == 0U) {
            continue;
        }
        if (cap.frame.wire.size() < header_bytes + name_len) {
            continue; // truncated frame, shouldn't happen
        }
        gossip_with_name++;

        // Extract name bytes.
        const std::string name(cap.frame.wire.begin() + static_cast<std::ptrdiff_t>(header_bytes),
                               cap.frame.wire.begin() + static_cast<std::ptrdiff_t>(header_bytes + name_len));

        // Extract hash from wire[8..15] (little-endian u64).
        std::uint64_t wire_hash = 0U;
        for (std::size_t b = 0U; b < 8U; b++) {
            wire_hash |= static_cast<std::uint64_t>(cap.frame.wire.at(8U + b)) << (b * 8U);
        }

        // Invariant 1: hash == rapidhash(name).
        const std::uint64_t computed_hash = rapidhash(name.data(), name.size());
        TEST_ASSERT_EQUAL_UINT64(computed_hash, wire_hash);

        // Invariant 2: no pin expression ('#') in gossiped name.
        TEST_ASSERT_EQUAL_size_t(std::string::npos, name.find('#'));

        // Invariant 3: no double separator.
        TEST_ASSERT_EQUAL_size_t(std::string::npos, name.find("//"));

        // Invariant 4: no leading or trailing separator.
        TEST_ASSERT_TRUE(name.front() != '/');
        TEST_ASSERT_TRUE(name.back() != '/');
    }

    // Sanity: we must have seen a reasonable number of gossip frames with names.
    TEST_ASSERT_TRUE(gossip_count > 0U);
    TEST_ASSERT_TRUE(gossip_with_name > 0U);

    e2e::cleanup_case(net,
                      now,
                      {},
                      { sub_basic, sub_slash, sub_pinned },
                      { pub_basic, pub_slash, pub_pinned },
                      step_us,
                      100'000,
                      100'000U);
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
    RUN_TEST(test_multinode_cohabitation_no_misdelivery);
    RUN_TEST(test_multinode_cohabitation_with_three_topics);
    RUN_TEST(test_older_unpinned_beats_newer_pinned);
    RUN_TEST(test_equal_lage_pinned_beats_unpinned_by_evictions);
    RUN_TEST(test_late_local_pin_request_does_not_rewrite_existing_topic);
    RUN_TEST(test_cohabitation_reliable_delivery);
    RUN_TEST(test_cohabitation_ordered_subscriber);
    RUN_TEST(test_gossip_names_normalized_and_hash_consistent);
    return UNITY_END();
}
