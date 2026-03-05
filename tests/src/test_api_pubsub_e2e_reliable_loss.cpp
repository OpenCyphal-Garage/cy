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
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace {

constexpr std::uint8_t header_msg_rel = 1U;
constexpr std::uint8_t header_msg_ack = 2U;

constexpr cy_us_t step_us          = 5'000;
constexpr cy_us_t ack_timeout_us   = 20'000;
constexpr cy_us_t publish_deadline = 260'000;
constexpr cy_us_t future_wait_us   = 800'000;

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

bool is_rel_a_to_b(const e2e::frame_info_t& frame)
{
    return (frame.source == e2e::sim_node_a) && (frame.destination == e2e::sim_node_b) &&
           (frame.header_type == header_msg_rel);
}

bool is_ack_b_to_a(const e2e::frame_info_t& frame)
{
    return (frame.source == e2e::sim_node_b) && (frame.destination == e2e::sim_node_a) &&
           (frame.header_type == header_msg_ack);
}

bool frame_payload_parse(const e2e::frame_info_t& frame, e2e::app_payload_t& out)
{
    if (frame.header_type != header_msg_rel) {
        return false;
    }
    return e2e::app_payload_unpack(frame.payload, out);
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

void assert_unordered_unique_only(const arrival_capture_t& capture, const std::uint32_t pub_id)
{
    const std::vector<std::uint64_t>  actual = sequences_for(capture, pub_id);
    std::unordered_set<std::uint64_t> unique{};
    for (const std::uint64_t s : actual) {
        TEST_ASSERT_TRUE(unique.insert(s).second);
    }
}

bool wait_all_futures(e2e::sim_net_t& net, cy_us_t& now, const std::vector<cy_future_t*>& futures)
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
            return true;
        }
        TEST_ASSERT_EQUAL_INT(CY_OK, e2e::drive_round(net, now, now));
        now += step_us;
    }
    return false;
}

void assert_publish_futures(const std::vector<cy_future_t*>& futures, const cy_err_t expected_error)
{
    for (cy_future_t* const fut : futures) {
        TEST_ASSERT_NOT_NULL(fut);
        TEST_ASSERT_TRUE(cy_future_done(fut));
        TEST_ASSERT_EQUAL_INT(expected_error, cy_future_error(fut));
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

void test_api_pubsub_e2e_b01_drop_first_data_frame_for_each_message()
{
    std::unordered_set<std::uint64_t> dropped{};
    e2e::fault_plan_t                 faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        return is_rel_a_to_b(frame) && frame.has_tag && dropped.insert(frame.tag).second;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB01U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b01/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b01/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 10U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 201U, seq, now, 350'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 120'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 201U, 1U, 10U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b02_drop_every_nth_data_frame()
{
    std::size_t       counter = 0U;
    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        if (!is_rel_a_to_b(frame)) {
            return false;
        }
        const bool drop = (counter % 4U) == 0U;
        counter++;
        return drop;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB02U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b02/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b02/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 10U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 202U, seq, now, 350'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 120'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 202U, 1U, 10U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b03_mid_stream_burst_data_loss_window()
{
    constexpr cy_us_t drop_window_begin = 40'000;
    constexpr cy_us_t drop_window_end   = 120'000;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        return is_rel_a_to_b(frame) && (frame.send_time >= drop_window_begin) && (frame.send_time <= drop_window_end);
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB03U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b03/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b03/topic", capture);

    std::vector<cy_future_t*> futures{};
    for (std::uint64_t seq = 1U; seq <= 10U; seq++) {
        set_now(net, now);
        cy_future_t* const fut = publish_reliable(pub, 203U, seq, now, 450'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
        drive_for(net, now, 15'000);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 140'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 203U, 1U, 10U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b04_drop_first_ack_for_each_message()
{
    std::unordered_set<std::uint64_t> dropped{};
    e2e::fault_plan_t                 faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        return is_ack_b_to_a(frame) && frame.has_tag && dropped.insert(frame.tag).second;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB04U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b04/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b04/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 10U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 204U, seq, now, 350'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 140'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 204U, 1U, 10U);
    assert_unordered_unique_only(capture, 204U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b05_drop_acks_for_first_k_retry_cycles_then_recover()
{
    constexpr std::size_t                          k = 2U;
    std::unordered_map<std::uint64_t, std::size_t> ack_attempts{};

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        if (!is_ack_b_to_a(frame) || !frame.has_tag) {
            return false;
        }
        std::size_t& attempts = ack_attempts[frame.tag];
        const bool   drop     = attempts < k;
        attempts++;
        return drop;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB05U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b05/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b05/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 205U, seq, now, 500'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 140'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 205U, 1U, 8U);
    assert_unordered_unique_only(capture, 205U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b06_mixed_data_and_ack_loss_pattern()
{
    std::unordered_map<std::uint64_t, std::uint64_t> seq_by_tag{};
    std::unordered_set<std::uint64_t>                dropped_data{};
    std::unordered_set<std::uint64_t>                dropped_ack{};

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        if (is_rel_a_to_b(frame) && frame.has_tag) {
            e2e::app_payload_t payload{};
            if (!frame_payload_parse(frame, payload)) {
                return false;
            }
            seq_by_tag[frame.tag] = payload.sequence;
            if (((payload.sequence % 2U) == 0U) && dropped_data.insert(frame.tag).second) {
                return true;
            }
        }
        if (is_ack_b_to_a(frame) && frame.has_tag) {
            const auto it = seq_by_tag.find(frame.tag);
            if ((it != seq_by_tag.end()) && ((it->second % 2U) != 0U) && dropped_ack.insert(frame.tag).second) {
                return true;
            }
        }
        return false;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB06U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b06/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b06/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 10U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 206U, seq, now, 420'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 140'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 206U, 1U, 10U);
    assert_unordered_unique_only(capture, 206U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b07_one_way_partition_a_to_b_then_heal_before_deadlines()
{
    constexpr cy_us_t partition_end = 120'000;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        return (frame.source == e2e::sim_node_a) && (frame.destination == e2e::sim_node_b) &&
               (frame.send_time <= partition_end);
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB07U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b07/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b07/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 207U, seq, now, 420'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 140'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 207U, 1U, 8U);
    assert_unordered_unique_only(capture, 207U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b08_one_way_partition_b_to_a_ack_blackout_then_heal()
{
    constexpr cy_us_t partition_end = 120'000;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        return is_ack_b_to_a(frame) && (frame.send_time <= partition_end);
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB08U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b08/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b08/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 208U, seq, now, 420'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 140'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 208U, 1U, 8U);
    assert_unordered_unique_only(capture, 208U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b09_full_partition_interval_then_heal_within_deadlines()
{
    constexpr cy_us_t partition_end = 120'000;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) { return frame.send_time <= partition_end; });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB09U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b09/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b09/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 209U, seq, now, 420'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 140'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 209U, 1U, 8U);
    assert_unordered_unique_only(capture, 209U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b10_partition_longer_than_deadline_expected_failures()
{
    constexpr cy_us_t partition_end = 300'000;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) { return frame.send_time <= partition_end; });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB10U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b10/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b10/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 6U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 210U, seq, now, 120'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 60'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_TRUE(sequences_for(capture, 210U).empty());
    assert_publish_futures(futures, CY_ERR_DELIVERY);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b11_late_ack_after_failure_does_not_resurrect_future()
{
    constexpr cy_us_t ack_delay = 220'000;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(faults, ack_delay, [](const e2e::frame_info_t& frame) { return is_ack_b_to_a(frame); });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB11U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b11/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b11/topic", capture);

    set_now(net, now);
    cy_future_t* const fut = publish_reliable(pub, 211U, 1U, now, 60'000);
    TEST_ASSERT_NOT_NULL(fut);

    const std::vector<cy_future_t*> futures = { fut };
    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    TEST_ASSERT_TRUE(cy_future_done(fut));
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(fut));

    drive_for(net, now, 320'000);
    TEST_ASSERT_TRUE(cy_future_done(fut));
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(fut));

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    assert_unordered_complete_unique(capture, 211U, 1U, 1U);
    assert_unordered_unique_only(capture, 211U);

    cleanup_case(net, now, futures, { sub }, { pub });
}

void test_api_pubsub_e2e_b12_transient_ack_send_media_failures_on_receiver_side_modeled_as_ack_egress_loss()
{
    constexpr std::size_t drop_first_acks = 8U;
    std::size_t           ack_seen        = 0U;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        if (!is_ack_b_to_a(frame)) {
            return false;
        }
        const bool drop = ack_seen < drop_first_acks;
        ack_seen++;
        return drop;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit), 0xB12U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const pub = make_publisher(net, "e2e/b12/topic");
    arrival_capture_t     capture{};
    cy_future_t* const    sub = make_subscriber(net, "e2e/b12/topic", capture);

    std::vector<cy_future_t*> futures{};
    set_now(net, now);
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        cy_future_t* const fut = publish_reliable(pub, 212U, seq, now, 450'000);
        TEST_ASSERT_NOT_NULL(fut);
        futures.push_back(fut);
    }

    TEST_ASSERT_TRUE(wait_all_futures(net, now, futures));
    drive_for(net, now, 160'000);

    TEST_ASSERT_EQUAL_size_t(0U, capture.malformed);
    TEST_ASSERT_EQUAL_size_t(drop_first_acks, std::min<std::size_t>(ack_seen, drop_first_acks));
    assert_unordered_complete_unique(capture, 212U, 1U, 8U);
    assert_unordered_unique_only(capture, 212U);
    assert_publish_futures(futures, CY_OK);

    cleanup_case(net, now, futures, { sub }, { pub });
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
    RUN_TEST(test_api_pubsub_e2e_b01_drop_first_data_frame_for_each_message);
    RUN_TEST(test_api_pubsub_e2e_b02_drop_every_nth_data_frame);
    RUN_TEST(test_api_pubsub_e2e_b03_mid_stream_burst_data_loss_window);
    RUN_TEST(test_api_pubsub_e2e_b04_drop_first_ack_for_each_message);
    RUN_TEST(test_api_pubsub_e2e_b05_drop_acks_for_first_k_retry_cycles_then_recover);
    RUN_TEST(test_api_pubsub_e2e_b06_mixed_data_and_ack_loss_pattern);
    RUN_TEST(test_api_pubsub_e2e_b07_one_way_partition_a_to_b_then_heal_before_deadlines);
    RUN_TEST(test_api_pubsub_e2e_b08_one_way_partition_b_to_a_ack_blackout_then_heal);
    RUN_TEST(test_api_pubsub_e2e_b09_full_partition_interval_then_heal_within_deadlines);
    RUN_TEST(test_api_pubsub_e2e_b10_partition_longer_than_deadline_expected_failures);
    RUN_TEST(test_api_pubsub_e2e_b11_late_ack_after_failure_does_not_resurrect_future);
    RUN_TEST(test_api_pubsub_e2e_b12_transient_ack_send_media_failures_on_receiver_side_modeled_as_ack_egress_loss);
    return UNITY_END();
}
