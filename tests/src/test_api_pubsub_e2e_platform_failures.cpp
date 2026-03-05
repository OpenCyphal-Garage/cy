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
#include <string>
#include <unordered_set>
#include <vector>

namespace {

constexpr cy_us_t step_us        = 5'000;
constexpr cy_us_t ack_timeout_us = 20'000;
constexpr cy_us_t wait_window_us = 1'200'000;

struct arrival_sample_t final
{
    std::uint32_t publisher_id{ 0U };
    std::uint64_t app_seq{ 0U };
};

struct arrival_capture_t final
{
    std::vector<arrival_sample_t> samples{};
    std::size_t                   malformed{ 0U };
    std::size_t                   first_malformed_size{ 0U };
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
        if (capture->first_malformed_size == 0U) {
            capture->first_malformed_size = size;
        }
        cy_message_refcount_dec(arrival.message.content);
        return;
    }
    capture->samples.push_back(arrival_sample_t{ .publisher_id = payload.publisher_id, .app_seq = payload.sequence });
    cy_message_refcount_dec(arrival.message.content);
}

void set_now(e2e::sim_net_t& net, const cy_us_t now)
{
    e2e::sim_net_node_now_set(net, e2e::sim_node_a, now);
    e2e::sim_net_node_now_set(net, e2e::sim_node_b, now);
}

void drive_for(e2e::sim_net_t& net, cy_us_t& now, const cy_us_t duration, const bool allow_spin_media_failures)
{
    const cy_us_t end = now + duration;
    while (now < end) {
        const cy_err_t err = e2e::drive_round(net, now, now);
        if (allow_spin_media_failures && (err == CY_ERR_MEDIA)) {
            now += step_us;
            continue;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, err);
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
        TEST_ASSERT_TRUE(guard < 30'000U);
    }
}

void drain_live_messages(e2e::sim_net_t& net, cy_us_t& now)
{
    std::size_t guard = 0U;
    while (cy_test_message_live_count() > 0U) {
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
        guard++;
        TEST_ASSERT_TRUE(guard < 30'000U);
    }
}

bool wait_all_futures(e2e::sim_net_t&                  net,
                      cy_us_t&                         now,
                      const std::vector<cy_future_t*>& futures,
                      const bool                       allow_spin_media_failures)
{
    const cy_us_t end = now + wait_window_us;
    while (now <= end) {
        bool all_done = true;
        for (cy_future_t* const fut : futures) {
            TEST_ASSERT_NOT_NULL(fut);
            if (!cy_future_done(fut)) {
                all_done = false;
                break;
            }
        }
        if (all_done) {
            return true;
        }
        const cy_err_t err = e2e::drive_round(net, now, now);
        if (allow_spin_media_failures && (err == CY_ERR_MEDIA)) {
            now += step_us;
            continue;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, err);
        now += step_us;
    }
    return false;
}

cy_publisher_t* make_publisher(e2e::sim_net_t& net, const char* const topic_name)
{
    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(pub);
    cy_ack_timeout_set(pub, ack_timeout_us);
    return pub;
}

cy_future_t* make_subscriber(e2e::sim_net_t& net, const char* const topic_name, arrival_capture_t& capture)
{
    cy_future_t* const sub = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_name), 64U);
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &capture;
    cy_future_context_set(sub, ctx);
    cy_future_callback_set(sub, on_arrival_capture);
    return sub;
}

cy_future_t* publish_reliable(cy_publisher_t* const pub,
                              const std::uint32_t   pub_id,
                              const std::uint64_t   app_seq,
                              const cy_us_t         now,
                              const cy_us_t         deadline_offset)
{
    const auto       payload = e2e::app_payload_pack(pub_id, app_seq);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    return cy_publish_reliable(pub, now + deadline_offset, msg);
}

cy_future_t* publish_reliable_retry(e2e::sim_net_t&     net,
                                    cy_us_t&            now,
                                    const bool          allow_spin_media_failures,
                                    cy_publisher_t*     pub,
                                    const std::uint32_t pub_id,
                                    const std::uint64_t app_seq,
                                    const cy_us_t       deadline_offset,
                                    const std::size_t   max_attempts = 256U)
{
    for (std::size_t attempt = 0U; attempt < max_attempts; attempt++) {
        set_now(net, now);
        cy_future_t* const fut = publish_reliable(pub, pub_id, app_seq, now, deadline_offset);
        if (fut != nullptr) {
            return fut;
        }
        drive_for(net, now, step_us, allow_spin_media_failures);
    }
    return nullptr;
}

std::vector<std::uint64_t> sequences_for(const arrival_capture_t& capture, const std::uint32_t pub_id)
{
    std::vector<std::uint64_t> out{};
    for (const arrival_sample_t& sample : capture.samples) {
        if (sample.publisher_id == pub_id) {
            out.push_back(sample.app_seq);
        }
    }
    return out;
}

void assert_unordered_complete_unique(const arrival_capture_t& capture,
                                      const std::uint32_t      pub_id,
                                      const std::uint64_t      first,
                                      const std::uint64_t      last)
{
    std::vector<std::uint64_t> actual = sequences_for(capture, pub_id);
    std::ranges::sort(actual);

    std::vector<std::uint64_t> expected{};
    for (std::uint64_t s = first; s <= last; s++) {
        expected.push_back(s);
    }

    if (expected.size() != actual.size()) {
        const std::string msg = "pub=" + std::to_string(pub_id) + " expected_count=" + std::to_string(expected.size()) +
                                " actual_count=" + std::to_string(actual.size());
        TEST_FAIL_MESSAGE(msg.c_str());
    }
    for (std::size_t i = 0U; i < expected.size(); i++) {
        if (expected.at(i) != actual.at(i)) {
            const std::string msg = "pub=" + std::to_string(pub_id) + " index=" + std::to_string(i) +
                                    " expected=" + std::to_string(expected.at(i)) +
                                    " actual=" + std::to_string(actual.at(i));
            TEST_FAIL_MESSAGE(msg.c_str());
        }
    }
}

void assert_unordered_unique_only(const arrival_capture_t& capture, const std::uint32_t pub_id)
{
    const std::vector<std::uint64_t>  actual = sequences_for(capture, pub_id);
    std::unordered_set<std::uint64_t> unique{};
    for (const std::uint64_t value : actual) {
        TEST_ASSERT_TRUE(unique.insert(value).second);
    }
}

void assert_no_malformed(const arrival_capture_t& capture, const char* const label)
{
    if (capture.malformed == 0U) {
        return;
    }
    const std::string msg = std::string(label) + " malformed=" + std::to_string(capture.malformed) +
                            " first_size=" + std::to_string(capture.first_malformed_size);
    TEST_FAIL_MESSAGE(msg.c_str());
}

void assert_future_error(const std::vector<cy_future_t*>& futures, const cy_err_t expected_error)
{
    for (cy_future_t* const fut : futures) {
        TEST_ASSERT_NOT_NULL(fut);
        TEST_ASSERT_TRUE(cy_future_done(fut));
        TEST_ASSERT_EQUAL_INT(expected_error, cy_future_error(fut));
    }
}

std::size_t count_failed_ops(const e2e::sim_net_t& net, const e2e::op_kind_t kind)
{
    const auto count =
      std::ranges::count_if(e2e::sim_net_op_fault_captures(net), [kind](const e2e::op_fault_capture_t& capture) {
          return capture.failed && (capture.op.kind == kind);
      });
    return static_cast<std::size_t>(count);
}

void cleanup_case(e2e::sim_net_t&                     net,
                  cy_us_t&                            now,
                  const std::vector<cy_future_t*>&    futures,
                  const std::vector<cy_future_t*>&    subscribers,
                  const std::vector<cy_publisher_t*>& publishers)
{
    e2e::sim_net_faults_set(net, nullptr, nullptr);

    for (cy_future_t* const fut : futures) {
        if (fut != nullptr) {
            cy_future_destroy(fut);
        }
    }

    for (cy_future_t* const sub : subscribers) {
        if (sub != nullptr) {
            cy_future_destroy(sub);
        }
    }
    drive_for(net, now, 40'000, false);

    for (cy_publisher_t* const pub : publishers) {
        if (pub != nullptr) {
            cy_unadvertise(pub);
        }
    }
    drive_for(net, now, 40'000, false);

    drain_queue(net, now);
    drain_live_messages(net, now);
    // Fault-injection scenarios can legitimately leave async error captures behind.
    // Teardown only requires transport/message/heap quiescence.
    e2e::assert_no_queued_frames(net);

    const std::size_t live_pre_deinit = cy_test_message_live_count();
    if (live_pre_deinit != 0U) {
        const std::string msg = "cleanup pre-deinit live_count=" + std::to_string(live_pre_deinit);
        TEST_FAIL_MESSAGE(msg.c_str());
    }

    e2e::sim_net_deinit(net);

    const std::size_t live_post_deinit = cy_test_message_live_count();
    if (live_post_deinit != 0U) {
        const std::string msg = "cleanup post-deinit live_count=" + std::to_string(live_post_deinit);
        TEST_FAIL_MESSAGE(msg.c_str());
    }

    for (std::size_t i = 0U; i < e2e::sim_net_node_count(net); i++) {
        const auto core_fragments = guarded_heap_allocated_fragments(&e2e::sim_net_core_heap(net, i));
        const auto core_bytes     = guarded_heap_allocated_bytes(&e2e::sim_net_core_heap(net, i));
        const auto msg_fragments  = guarded_heap_allocated_fragments(&e2e::sim_net_message_heap(net, i));
        const auto msg_bytes      = guarded_heap_allocated_bytes(&e2e::sim_net_message_heap(net, i));
        if ((core_fragments != 0U) || (core_bytes != 0U) || (msg_fragments != 0U) || (msg_bytes != 0U)) {
            const std::string msg =
              "cleanup heap leak node=" + std::to_string(i) + " core_fragments=" + std::to_string(core_fragments) +
              " core_bytes=" + std::to_string(core_bytes) + " msg_fragments=" + std::to_string(msg_fragments) +
              " msg_bytes=" + std::to_string(msg_bytes);
            TEST_FAIL_MESSAGE(msg.c_str());
        }
    }

    const std::size_t live_final = cy_test_message_live_count();
    if (live_final != 0U) {
        const std::string msg = "cleanup final live_count=" + std::to_string(live_final);
        TEST_FAIL_MESSAGE(msg.c_str());
    }
}

void test_api_pubsub_e2e_f01_transient_subject_send_failures_recover()
{
    std::size_t          remaining_failures = 10U;
    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, [&](const e2e::op_info_t& op) {
        if ((op.kind != e2e::op_kind_t::subject_send) || (op.node_index != e2e::sim_node_a)) {
            return false;
        }
        if (remaining_failures == 0U) {
            return false;
        }
        remaining_failures--;
        return true;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_op_faults_set(net, &op_faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/f01/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/f01/topic", capture);

    std::vector<cy_future_t*> futures{};
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable_retry(net, now, false, pub, 501U, seq, 600'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures, false));
    drive_for(net, now, 200'000, false);

    assert_no_malformed(capture, "f01");
    assert_unordered_complete_unique(capture, 501U, 1U, 8U);
    assert_unordered_unique_only(capture, 501U);
    assert_future_error(futures, CY_OK);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::subject_send) > 0U);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_f02_persistent_subject_send_failures_cause_future_failures()
{
    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(
      op_faults,
      CY_ERR_MEDIA,
      e2e::op_fault_predicate_all_of(
        { e2e::op_fault_predicate_kind(e2e::op_kind_t::subject_send), e2e::op_fault_predicate_node(e2e::sim_node_a) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_op_faults_set(net, &op_faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/f02/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/f02/topic", capture);

    std::vector<cy_future_t*> futures{};
    std::size_t               immediate_publish_failures = 0U;
    for (std::uint64_t seq = 1U; seq <= 6U; seq++) {
        set_now(net, now);
        cy_future_t* const fut = publish_reliable(pub, 502U, seq, now, 120'000);
        if (fut == nullptr) {
            immediate_publish_failures++;
            continue;
        }
        futures.push_back(fut);
    }

    if (!futures.empty()) {
        TEST_ASSERT_TRUE(wait_all_futures(net, now, futures, false));
    }
    drive_for(net, now, 60'000, false);

    assert_no_malformed(capture, "f02");
    TEST_ASSERT_TRUE(sequences_for(capture, 502U).empty());
    if (!futures.empty()) {
        assert_future_error(futures, CY_ERR_DELIVERY);
    }
    TEST_ASSERT_TRUE(immediate_publish_failures > 0U);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::subject_send) >= immediate_publish_failures);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_f03_transient_unicast_send_failures_on_receiver_recover()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));

    std::size_t          remaining_failures = 12U;
    const std::uint64_t  node_a_id          = e2e::sim_net_node_id(net, e2e::sim_node_a);
    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, [&](const e2e::op_info_t& op) {
        if ((op.kind != e2e::op_kind_t::unicast_send) || (op.node_index != e2e::sim_node_b) || !op.has_lane_id ||
            (op.lane_id != node_a_id)) {
            return false;
        }
        if (remaining_failures == 0U) {
            return false;
        }
        remaining_failures--;
        return true;
    });
    e2e::sim_net_op_faults_set(net, &op_faults);

    cy_us_t               now = 0;
    cy_publisher_t* const pub = make_publisher(net, "e2e/f03/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/f03/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 503U, seq, now, 700'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures, false));
    drive_for(net, now, 200'000, false);

    assert_no_malformed(capture, "f03");
    assert_unordered_complete_unique(capture, 503U, 1U, 8U);
    assert_unordered_unique_only(capture, 503U);
    assert_future_error(futures, CY_OK);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::unicast_send) > 0U);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_f04_mixed_subject_and_unicast_send_failures_still_converge()
{
    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(
      op_faults,
      CY_ERR_MEDIA,
      e2e::op_fault_predicate_all_of({ e2e::op_fault_predicate_kind(e2e::op_kind_t::subject_send),
                                       e2e::op_fault_predicate_node(e2e::sim_node_a),
                                       e2e::op_fault_predicate_every_nth(3U) }));
    e2e::op_fault_plan_add_fail(
      op_faults,
      CY_ERR_MEDIA,
      e2e::op_fault_predicate_all_of({ e2e::op_fault_predicate_kind(e2e::op_kind_t::unicast_send),
                                       e2e::op_fault_predicate_node(e2e::sim_node_b),
                                       e2e::op_fault_predicate_every_nth(4U) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_op_faults_set(net, &op_faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/f04/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/f04/topic", capture);

    std::vector<cy_future_t*> futures{};
    for (std::uint64_t seq = 1U; seq <= 10U; seq++) {
        cy_future_t* const fut = publish_reliable_retry(net, now, false, pub, 504U, seq, 800'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures, false));
    drive_for(net, now, 250'000, false);

    assert_no_malformed(capture, "f04");
    assert_unordered_complete_unique(capture, 504U, 1U, 10U);
    assert_unordered_unique_only(capture, 504U);
    assert_future_error(futures, CY_OK);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::subject_send) > 0U);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::unicast_send) > 0U);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_f05_transient_spin_failures_on_publisher_node_recover()
{
    std::size_t          remaining_failures = 40U;
    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, [&](const e2e::op_info_t& op) {
        if ((op.kind != e2e::op_kind_t::spin) || (op.node_index != e2e::sim_node_a)) {
            return false;
        }
        if (remaining_failures == 0U) {
            return false;
        }
        remaining_failures--;
        return true;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_op_faults_set(net, &op_faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/f05/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/f05/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 6U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 505U, seq, now, 900'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures, true));
    drive_for(net, now, 250'000, true);

    assert_no_malformed(capture, "f05");
    assert_unordered_complete_unique(capture, 505U, 1U, 6U);
    assert_unordered_unique_only(capture, 505U);
    assert_future_error(futures, CY_OK);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::spin) > 0U);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_f06_transient_spin_failures_on_subscriber_node_recover()
{
    std::size_t          remaining_failures = 50U;
    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, [&](const e2e::op_info_t& op) {
        if ((op.kind != e2e::op_kind_t::spin) || (op.node_index != e2e::sim_node_b)) {
            return false;
        }
        if (remaining_failures == 0U) {
            return false;
        }
        remaining_failures--;
        return true;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_op_faults_set(net, &op_faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/f06/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/f06/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 6U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 506U, seq, now, 900'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures, true));
    drive_for(net, now, 250'000, true);

    assert_no_malformed(capture, "f06");
    assert_unordered_complete_unique(capture, 506U, 1U, 6U);
    assert_unordered_unique_only(capture, 506U);
    assert_future_error(futures, CY_OK);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::spin) > 0U);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_f07_asymmetric_node_degradation_eventual_recovery()
{
    std::size_t          spin_failures = 20U;
    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(
      op_faults,
      CY_ERR_MEDIA,
      e2e::op_fault_predicate_all_of({ e2e::op_fault_predicate_kind(e2e::op_kind_t::subject_send),
                                       e2e::op_fault_predicate_node(e2e::sim_node_a),
                                       e2e::op_fault_predicate_every_nth(2U) }));
    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, [&](const e2e::op_info_t& op) {
        if ((op.kind != e2e::op_kind_t::spin) || (op.node_index != e2e::sim_node_b)) {
            return false;
        }
        if (spin_failures == 0U) {
            return false;
        }
        spin_failures--;
        return true;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_op_faults_set(net, &op_faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/f07/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/f07/topic", capture);

    std::vector<cy_future_t*> futures{};
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable_retry(net, now, true, pub, 507U, seq, 900'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures, true));
    drive_for(net, now, 250'000, true);

    assert_no_malformed(capture, "f07");
    assert_unordered_complete_unique(capture, 507U, 1U, 8U);
    assert_unordered_unique_only(capture, 507U);
    assert_future_error(futures, CY_OK);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::subject_send) > 0U);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::spin) > 0U);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_f08_failure_storm_then_recovery_preserves_invariants()
{
    std::size_t          subject_failures = 14U;
    std::size_t          unicast_failures = 14U;
    std::size_t          spin_failures    = 24U;
    e2e::op_fault_plan_t op_faults{};
    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, [&](const e2e::op_info_t& op) {
        if ((op.kind != e2e::op_kind_t::subject_send) || (op.node_index != e2e::sim_node_a)) {
            return false;
        }
        if (subject_failures == 0U) {
            return false;
        }
        subject_failures--;
        return true;
    });
    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, [&](const e2e::op_info_t& op) {
        if (op.kind != e2e::op_kind_t::unicast_send) {
            return false;
        }
        if (unicast_failures == 0U) {
            return false;
        }
        unicast_failures--;
        return true;
    });
    e2e::op_fault_plan_add_fail(op_faults, CY_ERR_MEDIA, [&](const e2e::op_info_t& op) {
        if (op.kind != e2e::op_kind_t::spin) {
            return false;
        }
        if (spin_failures == 0U) {
            return false;
        }
        spin_failures--;
        return true;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK, e2e::sim_net_init(net));
    e2e::sim_net_op_faults_set(net, &op_faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/f08/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/f08/topic", capture);

    std::vector<cy_future_t*> futures{};
    for (std::uint64_t seq = 1U; seq <= 10U; seq++) {
        cy_future_t* const fut = publish_reliable_retry(net, now, true, pub, 508U, seq, 1'000'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures, true));
    drive_for(net, now, 300'000, true);

    assert_no_malformed(capture, "f08");
    assert_unordered_complete_unique(capture, 508U, 1U, 10U);
    assert_unordered_unique_only(capture, 508U);
    assert_future_error(futures, CY_OK);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::subject_send) > 0U);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::unicast_send) > 0U);
    TEST_ASSERT_TRUE(count_failed_ops(net, e2e::op_kind_t::spin) > 0U);

    cleanup_case(net, now, futures, { sub }, { pub });
}

} // namespace

extern "C" void setUp()
{
    TEST_ASSERT_EQUAL_size_t_MESSAGE(0U, cy_test_message_live_count(), "setUp live_count must be zero");
    cy_test_message_reset_counters();
}

extern "C" void tearDown()
{
    TEST_ASSERT_EQUAL_size_t_MESSAGE(0U, cy_test_message_live_count(), "tearDown live_count must be zero");
}

int main()
{
    UNITY_BEGIN();
    RUN_TEST(test_api_pubsub_e2e_f01_transient_subject_send_failures_recover);
    RUN_TEST(test_api_pubsub_e2e_f02_persistent_subject_send_failures_cause_future_failures);
    RUN_TEST(test_api_pubsub_e2e_f03_transient_unicast_send_failures_on_receiver_recover);
    RUN_TEST(test_api_pubsub_e2e_f04_mixed_subject_and_unicast_send_failures_still_converge);
    RUN_TEST(test_api_pubsub_e2e_f05_transient_spin_failures_on_publisher_node_recover);
    RUN_TEST(test_api_pubsub_e2e_f06_transient_spin_failures_on_subscriber_node_recover);
    RUN_TEST(test_api_pubsub_e2e_f07_asymmetric_node_degradation_eventual_recovery);
    RUN_TEST(test_api_pubsub_e2e_f08_failure_storm_then_recovery_preserves_invariants);
    return UNITY_END();
}
