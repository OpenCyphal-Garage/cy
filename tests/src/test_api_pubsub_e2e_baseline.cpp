#include <cy_platform.h>
#include <unity.h>
#include "e2e_sim_net.hpp"
#include "e2e_test_utils.hpp"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace {

constexpr cy_us_t step_us          = 5'000;
constexpr cy_us_t ack_timeout_us   = 20'000;
constexpr cy_us_t future_wait_us   = 400'000;
constexpr cy_us_t ordered_window   = 30'000;
constexpr cy_us_t publish_deadline = 200'000;

struct arrival_sample_t final
{
    std::uint32_t publisher_id{ 0U };
    std::uint64_t app_seq{ 0U };
};

struct arrival_capture_t final
{
    std::vector<arrival_sample_t> samples{};
    std::size_t                   malformed{ 0U };
};

struct response_server_capture_t final
{
    std::size_t   count{ 0U };
    std::uint64_t first_message_tag{ 0U };
    std::uint64_t first_topic_hash{ 0U };
    cy_err_t      last_respond_error{ CY_OK };
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

    capture->samples.push_back(arrival_sample_t{ .publisher_id = payload.publisher_id, .app_seq = payload.sequence });
    cy_message_refcount_dec(arrival.message.content);
}

extern "C" void on_arrival_respond(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }

    auto* const capture = static_cast<response_server_capture_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(capture);

    capture->count++;
    if (capture->count == 1U) {
        capture->first_message_tag = arrival.breadcrumb.message_tag;
        capture->first_topic_hash  = arrival.breadcrumb.topic_hash;
    }

    const auto       payload    = e2e::app_payload_pack(109U, static_cast<std::uint64_t>(capture->count));
    const cy_bytes_t response   = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    cy_breadcrumb_t  breadcrumb = arrival.breadcrumb;
    capture->last_respond_error = cy_respond(&breadcrumb, arrival.message.timestamp + publish_deadline, response);
    cy_message_refcount_dec(arrival.message.content);
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

void set_now(e2e::sim_net_t& net, const cy_us_t now)
{
    e2e::sim_net_node_now_set(net, e2e::sim_node_a, now);
    e2e::sim_net_node_now_set(net, e2e::sim_node_b, now);
}

std::uint64_t read_u64_at(const std::vector<unsigned char>& wire, const std::size_t offset)
{
    TEST_ASSERT_TRUE(wire.size() >= (offset + 8U));
    std::uint64_t out = 0U;
    for (std::size_t i = 0U; i < 8U; i++) {
        out |= static_cast<std::uint64_t>(wire.at(offset + i)) << (i * 8U);
    }
    return out;
}

cy_publisher_t* make_publisher(e2e::sim_net_t& net, const char* const topic_name)
{
    cy_publisher_t* const pub = cy_advertise(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(pub);
    cy_ack_timeout_set(pub, ack_timeout_us);
    return pub;
}

cy_future_t* make_subscriber(e2e::sim_net_t&    net,
                             const char* const  topic_name,
                             const bool         ordered,
                             arrival_capture_t& capture)
{
    cy_future_t* sub = nullptr;
    if (ordered) {
        sub = cy_subscribe_ordered(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_name), 64U, ordered_window);
    } else {
        sub = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_name), 64U);
    }
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &capture;
    cy_future_context_set(sub, ctx);
    cy_future_callback_set(sub, on_arrival_capture);
    return sub;
}

cy_err_t publish_best_effort(cy_publisher_t* const pub,
                             const std::uint32_t   pub_id,
                             const std::uint64_t   app_seq,
                             const cy_us_t         now,
                             const cy_us_t         deadline_offset = publish_deadline)
{
    const auto       payload = e2e::app_payload_pack(pub_id, app_seq);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    return cy_publish(pub, now + deadline_offset, msg);
}

cy_future_t* publish_reliable(cy_publisher_t* const pub,
                              const std::uint32_t   pub_id,
                              const std::uint64_t   app_seq,
                              const cy_us_t         now,
                              const cy_us_t         deadline_offset = publish_deadline)
{
    const auto       payload = e2e::app_payload_pack(pub_id, app_seq);
    const cy_bytes_t msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    return cy_publish_reliable(pub, now + deadline_offset, msg);
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

    TEST_ASSERT_EQUAL_size_t(expected.size(), actual.size());
    for (std::size_t i = 0U; i < expected.size(); i++) {
        TEST_ASSERT_EQUAL_UINT64(expected.at(i), actual.at(i));
    }
}

void assert_ordered_strictly_increasing(const arrival_capture_t& capture, const std::uint32_t pub_id)
{
    bool          has_last = false;
    std::uint64_t last     = 0U;
    for (const arrival_sample_t& sample : capture.samples) {
        if (sample.publisher_id != pub_id) {
            continue;
        }
        if (has_last) {
            TEST_ASSERT_TRUE(sample.app_seq > last);
        }
        has_last = true;
        last     = sample.app_seq;
    }
}

void wait_all_futures(e2e::sim_net_t& net, cy_us_t& now, const std::vector<cy_future_t*>& futures)
{
    const cy_us_t end = now + future_wait_us;
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
            return;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }
}

void assert_publish_futures(const std::vector<cy_future_t*>& futures,
                            const cy_err_t                   expected_error,
                            const bool                       expected_delivered)
{
    for (cy_future_t* const fut : futures) {
        TEST_ASSERT_NOT_NULL(fut);
        TEST_ASSERT_TRUE(cy_future_done(fut));
        TEST_ASSERT_EQUAL_INT(expected_error, cy_future_error(fut));
        TEST_ASSERT_EQUAL_INT(expected_delivered ? 1 : 0, cy_publish_delivered(fut) ? 1 : 0);
    }
}

void cleanup_case(e2e::sim_net_t&                     net,
                  cy_us_t&                            now,
                  const std::vector<cy_future_t*>&    futures,
                  const std::vector<cy_future_t*>&    subscribers,
                  const std::vector<cy_publisher_t*>& publishers)
{
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
    drive_for(net, now, 40'000);

    for (cy_publisher_t* const pub : publishers) {
        if (pub != nullptr) {
            cy_unadvertise(pub);
        }
    }
    drive_for(net, now, 40'000);

    drain_queue(net, now);
    e2e::assert_quiescent(net);

    e2e::sim_net_deinit(net);
    e2e::assert_all_heaps_clean(net);
    e2e::assert_no_live_messages();
}

void test_api_pubsub_e2e_a01_best_effort_happy_unordered()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xA01U));
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/a01/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/a01/topic", false, capture);

    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 10U; seq++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, publish_best_effort(pub, 101U, seq, now));
    }

    drive_for(net, now, 120'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 101U, 1U, 10U);

    cleanup_case(net, now, {}, { sub }, { pub });
}

void test_api_pubsub_e2e_a02_best_effort_happy_ordered()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xA02U));
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/a02/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/a02/topic", true, capture);

    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 10U; seq++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, publish_best_effort(pub, 102U, seq, now));
    }

    drive_for(net, now, 120'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 102U, 1U, 10U);
    assert_ordered_strictly_increasing(capture, 102U);

    cleanup_case(net, now, {}, { sub }, { pub });
}

void test_api_pubsub_e2e_a03_reliable_happy_unordered()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xA03U));
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/a03/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/a03/topic", false, capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 103U, seq, now);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    wait_all_futures(net, now, futures);
    drive_for(net, now, 80'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 103U, 1U, 8U);
    assert_publish_futures(futures, CY_OK, true);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_a04_reliable_happy_ordered()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xA04U));
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/a04/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/a04/topic", true, capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 104U, seq, now);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    wait_all_futures(net, now, futures);
    drive_for(net, now, 80'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 104U, 1U, 8U);
    assert_ordered_strictly_increasing(capture, 104U);
    assert_publish_futures(futures, CY_OK, true);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_a05_reliable_burst_no_faults_unordered()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xA05U));
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/a05/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/a05/topic", false, capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 24U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 105U, seq, now, 350'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    wait_all_futures(net, now, futures);
    drive_for(net, now, 120'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 105U, 1U, 24U);
    assert_publish_futures(futures, CY_OK, true);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_a06_reliable_burst_no_faults_ordered()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xA06U));
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/a06/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/a06/topic", true, capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 24U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 106U, seq, now, 350'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    wait_all_futures(net, now, futures);
    drive_for(net, now, 120'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 106U, 1U, 24U);
    assert_ordered_strictly_increasing(capture, 106U);
    assert_publish_futures(futures, CY_OK, true);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_a07_late_subscriber_join_post_subscribe_only()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xA07U));
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/a07/topic");

    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 5U; seq++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, publish_best_effort(pub, 107U, seq, now));
    }
    drive_for(net, now, 80'000);

    arrival_capture_t  capture{};
    cy_future_t* const sub = make_subscriber(net, "e2e/a07/topic", false, capture);

    set_now(net, now);
    for (std::uint64_t seq = 6U; seq <= 10U; seq++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, publish_best_effort(pub, 107U, seq, now));
    }
    drive_for(net, now, 120'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 107U, 6U, 10U);

    cleanup_case(net, now, {}, { sub }, { pub });
}

void test_api_pubsub_e2e_a08_unsubscribe_resubscribe_during_active_publishing()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xA08U));
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/a08/topic");

    arrival_capture_t  first_capture{};
    cy_future_t* const first_sub = make_subscriber(net, "e2e/a08/topic", false, first_capture);

    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 4U; seq++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, publish_best_effort(pub, 108U, seq, now));
    }
    drive_for(net, now, 80'000);

    cy_future_destroy(first_sub);
    drive_for(net, now, 40'000);

    set_now(net, now);
    for (std::uint64_t seq = 5U; seq <= 8U; seq++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, publish_best_effort(pub, 108U, seq, now));
    }
    drive_for(net, now, 80'000);

    arrival_capture_t  second_capture{};
    cy_future_t* const second_sub = make_subscriber(net, "e2e/a08/topic", false, second_capture);

    set_now(net, now);
    for (std::uint64_t seq = 9U; seq <= 12U; seq++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, publish_best_effort(pub, 108U, seq, now));
    }
    drive_for(net, now, 120'000);

    TEST_ASSERT_EQUAL_size_t(0U, first_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, second_capture.malformed);
    assert_unordered_complete_unique(first_capture, 108U, 1U, 4U);
    assert_unordered_complete_unique(second_capture, 108U, 9U, 12U);

    cleanup_case(net, now, {}, { second_sub }, { pub });
}

void test_api_pubsub_e2e_a09_response_frame_metadata_is_parsed_per_response_header_layout()
{
    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xA09U));
    cy_us_t now = 0;

    static constexpr const char* topic_name = "e2e/a09/topic";
    cy_publisher_t* const client = cy_advertise_client(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(topic_name), 64U);
    TEST_ASSERT_NOT_NULL(client);
    cy_ack_timeout_set(client, ack_timeout_us);

    response_server_capture_t server_capture{};
    cy_future_t* const        server_sub = cy_subscribe(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_name), 64U);
    TEST_ASSERT_NOT_NULL(server_sub);

    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &server_capture;
    cy_future_context_set(server_sub, ctx);
    cy_future_callback_set(server_sub, on_arrival_respond);

    set_now(net, now);
    const auto         request_payload = e2e::app_payload_pack(909U, 1U);
    const cy_bytes_t   request_message = { .size = request_payload.size(),
                                           .data = request_payload.data(),
                                           .next = nullptr };
    cy_future_t* const request_future  = cy_request(client, now + 300'000, 200'000, request_message);
    TEST_ASSERT_NOT_NULL(request_future);

    wait_all_futures(net, now, { request_future });
    TEST_ASSERT_TRUE(cy_future_done(request_future));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(request_future));
    TEST_ASSERT_EQUAL_UINT64(1U, cy_response_count(request_future));
    TEST_ASSERT_EQUAL_size_t(1U, server_capture.count);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, server_capture.last_respond_error);

    const cy_response_t response = cy_response_move(request_future);
    TEST_ASSERT_NOT_NULL(response.message.content);
    cy_message_refcount_dec(response.message.content);

    const auto& captures = e2e::sim_net_captures(net);
    bool        found    = false;
    for (const e2e::frame_capture_t& cap : captures) {
        if ((cap.frame.source != e2e::sim_node_b) || (cap.frame.destination != e2e::sim_node_a) || !cap.frame.p2p ||
            (cap.frame.header_type != 3U)) {
            continue;
        }
        found = true;
        TEST_ASSERT_TRUE(cap.frame.has_tag);
        TEST_ASSERT_EQUAL_UINT64(0xFF, cap.frame.tag); // Best-effort responses currently use ack-correlation tag=255.
        TEST_ASSERT_TRUE(cap.frame.has_topic_hash);
        TEST_ASSERT_EQUAL_UINT64(server_capture.first_topic_hash, cap.frame.topic_hash);
        TEST_ASSERT_TRUE(cap.frame.wire.size() >= 24U);
        TEST_ASSERT_EQUAL_UINT8(0xFFU, cap.frame.wire.at(1U)); // Response tag at byte offset 1.
        TEST_ASSERT_EQUAL_UINT64(server_capture.first_message_tag, read_u64_at(cap.frame.wire, 16U));
        break;
    }
    TEST_ASSERT_TRUE(found);

    cleanup_case(net, now, { request_future }, { server_sub }, { client });
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
    RUN_TEST(test_api_pubsub_e2e_a01_best_effort_happy_unordered);
    RUN_TEST(test_api_pubsub_e2e_a02_best_effort_happy_ordered);
    RUN_TEST(test_api_pubsub_e2e_a03_reliable_happy_unordered);
    RUN_TEST(test_api_pubsub_e2e_a04_reliable_happy_ordered);
    RUN_TEST(test_api_pubsub_e2e_a05_reliable_burst_no_faults_unordered);
    RUN_TEST(test_api_pubsub_e2e_a06_reliable_burst_no_faults_ordered);
    RUN_TEST(test_api_pubsub_e2e_a07_late_subscriber_join_post_subscribe_only);
    RUN_TEST(test_api_pubsub_e2e_a08_unsubscribe_resubscribe_during_active_publishing);
    RUN_TEST(test_api_pubsub_e2e_a09_response_frame_metadata_is_parsed_per_response_header_layout);
    return UNITY_END();
}
