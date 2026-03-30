#include <cy_platform.h>
#include <unity.h>
#include "e2e_faults.hpp"
#include "e2e_sim_net.hpp"
#include "e2e_scenario_utils.hpp"
#include "e2e_test_utils.hpp"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace {

constexpr std::uint8_t header_msg_rel = 1U;
constexpr std::uint8_t header_msg_ack = 2U;

constexpr cy_us_t step_us             = 1'000;
constexpr cy_us_t ack_timeout_us      = 20'000;
constexpr cy_us_t ordered_window_us   = 20'000;
constexpr cy_us_t default_deadline_us = 300'000;
constexpr cy_us_t future_wait_us      = 900'000;

using e2e::arrival_capture_t;
using e2e::arrival_sample_t;
using e2e::on_arrival_capture;

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
        sub = cy_subscribe_ordered(e2e::sim_net_cy(net, e2e::sim_node_b), cy_str(topic_name), 64U, ordered_window_us);
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

std::uint64_t topic_hash_for(e2e::sim_net_t& net, const char* const topic_name)
{
    const cy_topic_t* const topic = cy_topic_find_by_name(e2e::sim_net_cy(net, e2e::sim_node_a), cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(topic);
    return cy_topic_hash(topic);
}

cy_future_t* publish_reliable(cy_publisher_t* const pub,
                              const std::uint32_t   pub_id,
                              const std::uint64_t   app_seq,
                              const cy_us_t         now,
                              const cy_us_t         deadline_offset = default_deadline_us)
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
            out.push_back(sample.sequence);
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

void assert_ordered_strictly_increasing(const arrival_capture_t& capture, const std::uint32_t pub_id)
{
    bool          has_last = false;
    std::uint64_t last     = 0U;
    for (const arrival_sample_t& sample : capture.samples) {
        if (sample.publisher_id != pub_id) {
            continue;
        }
        if (has_last) {
            TEST_ASSERT_TRUE(sample.sequence > last);
        }
        has_last = true;
        last     = sample.sequence;
    }
}

void test_api_pubsub_e2e_c01_ack_loss_retransmit_duplicate_rejected_unordered()
{
    constexpr std::uint32_t hot_pub_id  = 301U;
    constexpr std::uint32_t cold_pub_id = 302U;

    std::uint64_t                     hot_hash = 0U;
    std::unordered_set<std::uint64_t> dropped_hot_ack{};

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        return is_ack_b_to_a(frame) && frame.has_topic_hash && (frame.topic_hash == hot_hash) && frame.has_tag &&
               dropped_hot_ack.insert(frame.tag).second;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC01U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c01/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c01/cold");
    hot_hash                       = topic_hash_for(net, "e2e/c01/hot");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c01/hot", false, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c01/cold", false, cold_capture);

    std::vector<cy_future_t*> hot_futures{};
    std::vector<cy_future_t*> cold_futures{};
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        e2e::set_now(net, now);
        cy_future_t* const hot_fut  = publish_reliable(hot_pub, hot_pub_id, seq, now, 420'000);
        cy_future_t* const cold_fut = publish_reliable(cold_pub, cold_pub_id, seq, now, 420'000);
        TEST_ASSERT_NOT_NULL(hot_fut);
        TEST_ASSERT_NOT_NULL(cold_fut);
        hot_futures.push_back(hot_fut);
        cold_futures.push_back(cold_fut);
    }

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 140'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);
    assert_unordered_complete_unique(hot_capture, hot_pub_id, 1U, 8U);
    assert_unordered_complete_unique(cold_capture, cold_pub_id, 1U, 8U);
    assert_unordered_unique_only(hot_capture, hot_pub_id);
    assert_unordered_unique_only(cold_capture, cold_pub_id);
    e2e::assert_future_error(hot_futures, CY_OK);
    e2e::assert_future_error(cold_futures, CY_OK);

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
}

void test_api_pubsub_e2e_c02_ack_loss_retransmit_duplicate_rejected_ordered()
{
    constexpr std::uint32_t hot_pub_id  = 303U;
    constexpr std::uint32_t cold_pub_id = 304U;

    std::uint64_t                     hot_hash = 0U;
    std::unordered_set<std::uint64_t> dropped_hot_ack{};

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        return is_ack_b_to_a(frame) && frame.has_topic_hash && (frame.topic_hash == hot_hash) && frame.has_tag &&
               dropped_hot_ack.insert(frame.tag).second;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC02U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c02/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c02/cold");
    hot_hash                       = topic_hash_for(net, "e2e/c02/hot");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c02/hot", true, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c02/cold", true, cold_capture);

    std::vector<cy_future_t*> hot_futures{};
    std::vector<cy_future_t*> cold_futures{};
    for (std::uint64_t seq = 1U; seq <= 8U; seq++) {
        e2e::set_now(net, now);
        cy_future_t* const hot_fut  = publish_reliable(hot_pub, hot_pub_id, seq, now, 420'000);
        cy_future_t* const cold_fut = publish_reliable(cold_pub, cold_pub_id, seq, now, 420'000);
        TEST_ASSERT_NOT_NULL(hot_fut);
        TEST_ASSERT_NOT_NULL(cold_fut);
        hot_futures.push_back(hot_fut);
        cold_futures.push_back(cold_fut);
    }

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 140'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);
    assert_unordered_complete_unique(hot_capture, hot_pub_id, 1U, 8U);
    assert_unordered_complete_unique(cold_capture, cold_pub_id, 1U, 8U);
    assert_ordered_strictly_increasing(hot_capture, hot_pub_id);
    assert_ordered_strictly_increasing(cold_capture, cold_pub_id);
    e2e::assert_future_error(hot_futures, CY_OK);
    e2e::assert_future_error(cold_futures, CY_OK);

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
}

void test_api_pubsub_e2e_c03_retransmit_overtakes_newer_message_unordered_unique()
{
    constexpr std::uint32_t hot_pub_id  = 305U;
    constexpr std::uint32_t cold_pub_id = 306U;

    std::uint64_t                                  hot_hash = 0U;
    std::optional<std::uint64_t>                   hot_seq1_tag{};
    std::unordered_map<std::uint64_t, std::size_t> hot_attempts{};
    bool                                           dropped_hot_ack = false;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(faults, 60'000, [&](const e2e::frame_info_t& frame) {
        if (!is_rel_a_to_b(frame) || !frame.has_topic_hash || (frame.topic_hash != hot_hash) || !frame.has_tag) {
            return false;
        }
        e2e::app_payload_t payload{};
        if (!frame_payload_parse(frame, payload) || (payload.publisher_id != hot_pub_id) || (payload.sequence != 1U)) {
            return false;
        }
        if (!hot_seq1_tag.has_value()) {
            hot_seq1_tag = frame.tag;
        }
        std::size_t& attempts = hot_attempts[frame.tag];
        attempts++;
        return hot_seq1_tag.has_value() && (frame.tag == *hot_seq1_tag) && (attempts > 1U);
    });
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        if (!is_ack_b_to_a(frame) || !frame.has_topic_hash || (frame.topic_hash != hot_hash) || !frame.has_tag ||
            !hot_seq1_tag.has_value() || dropped_hot_ack) {
            return false;
        }
        if (frame.tag == *hot_seq1_tag) {
            dropped_hot_ack = true;
            return true;
        }
        return false;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC03U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c03/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c03/cold");
    hot_hash                       = topic_hash_for(net, "e2e/c03/hot");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c03/hot", false, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c03/cold", false, cold_capture);

    std::vector<cy_future_t*> hot_futures{};
    std::vector<cy_future_t*> cold_futures{};

    e2e::set_now(net, now);
    cy_future_t* const hot_fut_1  = publish_reliable(hot_pub, hot_pub_id, 1U, now, 420'000);
    cy_future_t* const cold_fut_1 = publish_reliable(cold_pub, cold_pub_id, 1U, now, 420'000);
    TEST_ASSERT_NOT_NULL(hot_fut_1);
    TEST_ASSERT_NOT_NULL(cold_fut_1);
    hot_futures.push_back(hot_fut_1);
    cold_futures.push_back(cold_fut_1);

    e2e::drive_for(net, now, 2'000, step_us);

    e2e::set_now(net, now);
    cy_future_t* const hot_fut_2  = publish_reliable(hot_pub, hot_pub_id, 2U, now, 420'000);
    cy_future_t* const cold_fut_2 = publish_reliable(cold_pub, cold_pub_id, 2U, now, 420'000);
    TEST_ASSERT_NOT_NULL(hot_fut_2);
    TEST_ASSERT_NOT_NULL(cold_fut_2);
    hot_futures.push_back(hot_fut_2);
    cold_futures.push_back(cold_fut_2);

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 180'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);
    assert_unordered_complete_unique(hot_capture, hot_pub_id, 1U, 2U);
    assert_unordered_complete_unique(cold_capture, cold_pub_id, 1U, 2U);
    assert_unordered_unique_only(hot_capture, hot_pub_id);
    assert_unordered_unique_only(cold_capture, cold_pub_id);
    e2e::assert_future_error(hot_futures, CY_OK);
    e2e::assert_future_error(cold_futures, CY_OK);

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
}

void test_api_pubsub_e2e_c04_retransmit_overtakes_newer_message_ordered_restored()
{
    constexpr std::uint32_t hot_pub_id  = 307U;
    constexpr std::uint32_t cold_pub_id = 308U;

    std::uint64_t                                  hot_hash = 0U;
    std::optional<std::uint64_t>                   hot_seq1_tag{};
    std::unordered_map<std::uint64_t, std::size_t> hot_attempts{};
    bool                                           dropped_hot_ack = false;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(faults, 60'000, [&](const e2e::frame_info_t& frame) {
        if (!is_rel_a_to_b(frame) || !frame.has_topic_hash || (frame.topic_hash != hot_hash) || !frame.has_tag) {
            return false;
        }
        e2e::app_payload_t payload{};
        if (!frame_payload_parse(frame, payload) || (payload.publisher_id != hot_pub_id) || (payload.sequence != 1U)) {
            return false;
        }
        if (!hot_seq1_tag.has_value()) {
            hot_seq1_tag = frame.tag;
        }
        std::size_t& attempts = hot_attempts[frame.tag];
        attempts++;
        return hot_seq1_tag.has_value() && (frame.tag == *hot_seq1_tag) && (attempts > 1U);
    });
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        if (!is_ack_b_to_a(frame) || !frame.has_topic_hash || (frame.topic_hash != hot_hash) || !frame.has_tag ||
            !hot_seq1_tag.has_value() || dropped_hot_ack) {
            return false;
        }
        if (frame.tag == *hot_seq1_tag) {
            dropped_hot_ack = true;
            return true;
        }
        return false;
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC04U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c04/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c04/cold");
    hot_hash                       = topic_hash_for(net, "e2e/c04/hot");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c04/hot", true, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c04/cold", true, cold_capture);

    std::vector<cy_future_t*> hot_futures{};
    std::vector<cy_future_t*> cold_futures{};

    e2e::set_now(net, now);
    cy_future_t* const hot_fut_1  = publish_reliable(hot_pub, hot_pub_id, 1U, now, 420'000);
    cy_future_t* const cold_fut_1 = publish_reliable(cold_pub, cold_pub_id, 1U, now, 420'000);
    TEST_ASSERT_NOT_NULL(hot_fut_1);
    TEST_ASSERT_NOT_NULL(cold_fut_1);
    hot_futures.push_back(hot_fut_1);
    cold_futures.push_back(cold_fut_1);

    e2e::drive_for(net, now, 2'000, step_us);

    e2e::set_now(net, now);
    cy_future_t* const hot_fut_2  = publish_reliable(hot_pub, hot_pub_id, 2U, now, 420'000);
    cy_future_t* const cold_fut_2 = publish_reliable(cold_pub, cold_pub_id, 2U, now, 420'000);
    TEST_ASSERT_NOT_NULL(hot_fut_2);
    TEST_ASSERT_NOT_NULL(cold_fut_2);
    hot_futures.push_back(hot_fut_2);
    cold_futures.push_back(cold_fut_2);

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 180'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);
    assert_unordered_complete_unique(hot_capture, hot_pub_id, 1U, 2U);
    assert_unordered_complete_unique(cold_capture, cold_pub_id, 1U, 2U);
    assert_ordered_strictly_increasing(hot_capture, hot_pub_id);
    assert_ordered_strictly_increasing(cold_capture, cold_pub_id);
    e2e::assert_future_error(hot_futures, CY_OK);
    e2e::assert_future_error(cold_futures, CY_OK);

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
}

void test_api_pubsub_e2e_c05_ordered_gap_timeout_flush()
{
    constexpr std::uint32_t hot_pub_id  = 309U;
    constexpr std::uint32_t cold_pub_id = 310U;

    std::uint64_t hot_hash = 0U;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_drop(faults, [&](const e2e::frame_info_t& frame) {
        if (!is_rel_a_to_b(frame) || !frame.has_topic_hash || (frame.topic_hash != hot_hash)) {
            return false;
        }
        e2e::app_payload_t payload{};
        return frame_payload_parse(frame, payload) && (payload.publisher_id == hot_pub_id) && (payload.sequence == 1U);
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC05U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c05/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c05/cold");
    hot_hash                       = topic_hash_for(net, "e2e/c05/hot");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c05/hot", true, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c05/cold", true, cold_capture);

    e2e::set_now(net, now);
    cy_future_t* const hot_fut_1  = publish_reliable(hot_pub, hot_pub_id, 1U, now, 90'000);
    cy_future_t* const cold_fut_1 = publish_reliable(cold_pub, cold_pub_id, 1U, now, 300'000);
    cy_future_t* const hot_fut_2  = publish_reliable(hot_pub, hot_pub_id, 2U, now, 300'000);
    cy_future_t* const cold_fut_2 = publish_reliable(cold_pub, cold_pub_id, 2U, now, 300'000);

    TEST_ASSERT_NOT_NULL(hot_fut_1);
    TEST_ASSERT_NOT_NULL(cold_fut_1);
    TEST_ASSERT_NOT_NULL(hot_fut_2);
    TEST_ASSERT_NOT_NULL(cold_fut_2);

    const std::vector<cy_future_t*> hot_futures  = { hot_fut_1, hot_fut_2 };
    const std::vector<cy_future_t*> cold_futures = { cold_fut_1, cold_fut_2 };

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 120'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);
    assert_unordered_complete_unique(hot_capture, hot_pub_id, 2U, 2U);
    assert_unordered_complete_unique(cold_capture, cold_pub_id, 1U, 2U);
    assert_ordered_strictly_increasing(hot_capture, hot_pub_id);
    assert_ordered_strictly_increasing(cold_capture, cold_pub_id);
    TEST_ASSERT_TRUE(cy_future_done(hot_fut_1));
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(hot_fut_1));
    TEST_ASSERT_TRUE(cy_future_done(hot_fut_2));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(hot_fut_2));
    TEST_ASSERT_TRUE(cy_future_done(cold_fut_1));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(cold_fut_1));
    TEST_ASSERT_TRUE(cy_future_done(cold_fut_2));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(cold_fut_2));

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
}

void test_api_pubsub_e2e_c06_late_older_frame_after_timeout_rejected()
{
    constexpr std::uint32_t hot_pub_id  = 311U;
    constexpr std::uint32_t cold_pub_id = 312U;

    std::uint64_t hot_hash = 0U;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(faults, 50'000, [&](const e2e::frame_info_t& frame) {
        if (!is_rel_a_to_b(frame) || !frame.has_topic_hash || (frame.topic_hash != hot_hash)) {
            return false;
        }
        e2e::app_payload_t payload{};
        return frame_payload_parse(frame, payload) && (payload.publisher_id == hot_pub_id) && (payload.sequence == 1U);
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC06U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c06/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c06/cold");
    hot_hash                       = topic_hash_for(net, "e2e/c06/hot");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c06/hot", true, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c06/cold", true, cold_capture);

    e2e::set_now(net, now);
    cy_future_t* const hot_fut_1  = publish_reliable(hot_pub, hot_pub_id, 1U, now, 300'000);
    cy_future_t* const cold_fut_1 = publish_reliable(cold_pub, cold_pub_id, 1U, now, 300'000);
    cy_future_t* const hot_fut_2  = publish_reliable(hot_pub, hot_pub_id, 2U, now, 300'000);
    cy_future_t* const cold_fut_2 = publish_reliable(cold_pub, cold_pub_id, 2U, now, 300'000);

    TEST_ASSERT_NOT_NULL(hot_fut_1);
    TEST_ASSERT_NOT_NULL(cold_fut_1);
    TEST_ASSERT_NOT_NULL(hot_fut_2);
    TEST_ASSERT_NOT_NULL(cold_fut_2);

    const std::vector<cy_future_t*> hot_futures  = { hot_fut_1, hot_fut_2 };
    const std::vector<cy_future_t*> cold_futures = { cold_fut_1, cold_fut_2 };

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 140'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);
    assert_unordered_complete_unique(hot_capture, hot_pub_id, 2U, 2U);
    assert_unordered_complete_unique(cold_capture, cold_pub_id, 1U, 2U);
    assert_ordered_strictly_increasing(hot_capture, hot_pub_id);
    assert_ordered_strictly_increasing(cold_capture, cold_pub_id);
    e2e::assert_future_error(hot_futures, CY_OK);
    e2e::assert_future_error(cold_futures, CY_OK);

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
}

void test_api_pubsub_e2e_c07_ordered_buffer_capacity_stress_large_jump_backfill()
{
    constexpr std::uint32_t hot_pub_id  = 313U;
    constexpr std::uint32_t cold_pub_id = 314U;

    std::uint64_t hot_hash = 0U;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(faults, 120'000, [&](const e2e::frame_info_t& frame) {
        if (!is_rel_a_to_b(frame) || !frame.has_topic_hash || (frame.topic_hash != hot_hash)) {
            return false;
        }
        e2e::app_payload_t payload{};
        return frame_payload_parse(frame, payload) && (payload.publisher_id == hot_pub_id) && (payload.sequence <= 20U);
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC07U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c07/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c07/cold");
    hot_hash                       = topic_hash_for(net, "e2e/c07/hot");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c07/hot", true, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c07/cold", true, cold_capture);

    std::vector<cy_future_t*> hot_futures{};
    std::vector<cy_future_t*> cold_futures{};

    for (std::uint64_t seq = 1U; seq <= 30U; seq++) {
        e2e::set_now(net, now);
        cy_future_t* const hot_fut = publish_reliable(hot_pub, hot_pub_id, seq, now, 650'000);
        TEST_ASSERT_NOT_NULL(hot_fut);
        hot_futures.push_back(hot_fut);

        if (seq <= 12U) {
            cy_future_t* const cold_fut = publish_reliable(cold_pub, cold_pub_id, seq, now, 650'000);
            TEST_ASSERT_NOT_NULL(cold_fut);
            cold_futures.push_back(cold_fut);
        }
    }

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 220'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);

    const std::vector<std::uint64_t> hot_sequences = sequences_for(hot_capture, hot_pub_id);
    assert_unordered_unique_only(hot_capture, hot_pub_id);
    TEST_ASSERT_TRUE(!hot_sequences.empty());
    TEST_ASSERT_TRUE(hot_sequences.size() >= 10U);
    TEST_ASSERT_TRUE(std::ranges::any_of(hot_sequences, [](const std::uint64_t seq) { return seq >= 21U; }));
    for (const std::uint64_t seq : hot_sequences) {
        TEST_ASSERT_TRUE((seq >= 1U) && (seq <= 30U));
    }
    assert_ordered_strictly_increasing(hot_capture, hot_pub_id);

    assert_unordered_complete_unique(cold_capture, cold_pub_id, 1U, 12U);
    assert_ordered_strictly_increasing(cold_capture, cold_pub_id);
    e2e::assert_future_error(hot_futures, CY_OK);
    e2e::assert_future_error(cold_futures, CY_OK);

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
}

void test_api_pubsub_e2e_c08_high_jitter_moderate_loss_ordered_monotonicity()
{
    constexpr std::uint32_t hot_pub_id  = 315U;
    constexpr std::uint32_t cold_pub_id = 316U;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(
      faults,
      6'000,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(header_msg_rel),
                                                                  e2e::fault_predicate_header_type(header_msg_ack) }),
                                    e2e::fault_predicate_every_nth(2U) }));
    e2e::fault_plan_add_delay(
      faults,
      11'000,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(header_msg_rel),
                                                                  e2e::fault_predicate_header_type(header_msg_ack) }),
                                    e2e::fault_predicate_every_nth(3U) }));
    e2e::fault_plan_add_delay(
      faults,
      17'000,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(header_msg_rel),
                                                                  e2e::fault_predicate_header_type(header_msg_ack) }),
                                    e2e::fault_predicate_every_nth(5U) }));
    e2e::fault_plan_add_drop(faults,
                             e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(header_msg_rel),
                                                           e2e::fault_predicate_every_nth(9U) }));
    e2e::fault_plan_add_drop(faults,
                             e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(header_msg_ack),
                                                           e2e::fault_predicate_every_nth(11U) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC08U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c08/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c08/cold");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c08/hot", true, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c08/cold", true, cold_capture);

    std::vector<cy_future_t*> hot_futures{};
    std::vector<cy_future_t*> cold_futures{};
    for (std::uint64_t seq = 1U; seq <= 14U; seq++) {
        e2e::set_now(net, now);
        cy_future_t* const hot_fut  = publish_reliable(hot_pub, hot_pub_id, seq, now, 700'000);
        cy_future_t* const cold_fut = publish_reliable(cold_pub, cold_pub_id, seq, now, 700'000);
        TEST_ASSERT_NOT_NULL(hot_fut);
        TEST_ASSERT_NOT_NULL(cold_fut);
        hot_futures.push_back(hot_fut);
        cold_futures.push_back(cold_fut);
    }

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 220'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);
    assert_unordered_unique_only(hot_capture, hot_pub_id);
    assert_unordered_unique_only(cold_capture, cold_pub_id);
    assert_ordered_strictly_increasing(hot_capture, hot_pub_id);
    assert_ordered_strictly_increasing(cold_capture, cold_pub_id);
    TEST_ASSERT_TRUE(sequences_for(hot_capture, hot_pub_id).size() >= 10U);
    TEST_ASSERT_TRUE(sequences_for(cold_capture, cold_pub_id).size() >= 10U);
    e2e::assert_future_error(hot_futures, CY_OK);
    e2e::assert_future_error(cold_futures, CY_OK);

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
}

void test_api_pubsub_e2e_c09_high_jitter_moderate_loss_unordered_completeness()
{
    constexpr std::uint32_t hot_pub_id  = 317U;
    constexpr std::uint32_t cold_pub_id = 318U;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(
      faults,
      6'000,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(header_msg_rel),
                                                                  e2e::fault_predicate_header_type(header_msg_ack) }),
                                    e2e::fault_predicate_every_nth(2U) }));
    e2e::fault_plan_add_delay(
      faults,
      11'000,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(header_msg_rel),
                                                                  e2e::fault_predicate_header_type(header_msg_ack) }),
                                    e2e::fault_predicate_every_nth(3U) }));
    e2e::fault_plan_add_delay(
      faults,
      17'000,
      e2e::fault_predicate_all_of({ e2e::fault_predicate_any_of({ e2e::fault_predicate_header_type(header_msg_rel),
                                                                  e2e::fault_predicate_header_type(header_msg_ack) }),
                                    e2e::fault_predicate_every_nth(5U) }));
    e2e::fault_plan_add_drop(faults,
                             e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(header_msg_rel),
                                                           e2e::fault_predicate_every_nth(9U) }));
    e2e::fault_plan_add_drop(faults,
                             e2e::fault_predicate_all_of({ e2e::fault_predicate_header_type(header_msg_ack),
                                                           e2e::fault_predicate_every_nth(11U) }));

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC09U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c09/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c09/cold");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c09/hot", false, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c09/cold", false, cold_capture);

    std::vector<cy_future_t*> hot_futures{};
    std::vector<cy_future_t*> cold_futures{};
    for (std::uint64_t seq = 1U; seq <= 14U; seq++) {
        e2e::set_now(net, now);
        cy_future_t* const hot_fut  = publish_reliable(hot_pub, hot_pub_id, seq, now, 700'000);
        cy_future_t* const cold_fut = publish_reliable(cold_pub, cold_pub_id, seq, now, 700'000);
        TEST_ASSERT_NOT_NULL(hot_fut);
        TEST_ASSERT_NOT_NULL(cold_fut);
        hot_futures.push_back(hot_fut);
        cold_futures.push_back(cold_fut);
    }

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 220'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);
    assert_unordered_complete_unique(hot_capture, hot_pub_id, 1U, 14U);
    assert_unordered_complete_unique(cold_capture, cold_pub_id, 1U, 14U);
    assert_unordered_unique_only(hot_capture, hot_pub_id);
    assert_unordered_unique_only(cold_capture, cold_pub_id);
    e2e::assert_future_error(hot_futures, CY_OK);
    e2e::assert_future_error(cold_futures, CY_OK);

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
}

void test_api_pubsub_e2e_c10_reordering_window_boundary_behavior()
{
    constexpr std::uint32_t hot_pub_id  = 319U;
    constexpr std::uint32_t cold_pub_id = 320U;

    std::uint64_t hot_hash  = 0U;
    std::uint64_t cold_hash = 0U;

    e2e::fault_plan_t faults{};
    e2e::fault_plan_add_delay(faults, ordered_window_us - 2'000, [&](const e2e::frame_info_t& frame) {
        if (!is_rel_a_to_b(frame) || !frame.has_topic_hash || (frame.topic_hash != hot_hash)) {
            return false;
        }
        e2e::app_payload_t payload{};
        return frame_payload_parse(frame, payload) && (payload.publisher_id == hot_pub_id) && (payload.sequence == 1U);
    });
    e2e::fault_plan_add_delay(faults, ordered_window_us + 8'000, [&](const e2e::frame_info_t& frame) {
        if (!is_rel_a_to_b(frame) || !frame.has_topic_hash || (frame.topic_hash != cold_hash)) {
            return false;
        }
        e2e::app_payload_t payload{};
        return frame_payload_parse(frame, payload) && (payload.publisher_id == cold_pub_id) && (payload.sequence == 1U);
    });

    e2e::sim_net_t net{};
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          e2e::sim_net_init(net, static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit), 0xC10U));
    e2e::sim_net_faults_set(net, &faults);
    cy_us_t now = 0;

    cy_publisher_t* const hot_pub  = make_publisher(net, "e2e/c10/hot");
    cy_publisher_t* const cold_pub = make_publisher(net, "e2e/c10/cold");
    hot_hash                       = topic_hash_for(net, "e2e/c10/hot");
    cold_hash                      = topic_hash_for(net, "e2e/c10/cold");

    arrival_capture_t  hot_capture{};
    arrival_capture_t  cold_capture{};
    cy_future_t* const hot_sub  = make_subscriber(net, "e2e/c10/hot", true, hot_capture);
    cy_future_t* const cold_sub = make_subscriber(net, "e2e/c10/cold", true, cold_capture);

    e2e::set_now(net, now);
    cy_future_t* const hot_fut_1  = publish_reliable(hot_pub, hot_pub_id, 1U, now, 420'000);
    cy_future_t* const cold_fut_1 = publish_reliable(cold_pub, cold_pub_id, 1U, now, 420'000);
    cy_future_t* const hot_fut_2  = publish_reliable(hot_pub, hot_pub_id, 2U, now, 420'000);
    cy_future_t* const cold_fut_2 = publish_reliable(cold_pub, cold_pub_id, 2U, now, 420'000);

    TEST_ASSERT_NOT_NULL(hot_fut_1);
    TEST_ASSERT_NOT_NULL(cold_fut_1);
    TEST_ASSERT_NOT_NULL(hot_fut_2);
    TEST_ASSERT_NOT_NULL(cold_fut_2);

    const std::vector<cy_future_t*> hot_futures  = { hot_fut_1, hot_fut_2 };
    const std::vector<cy_future_t*> cold_futures = { cold_fut_1, cold_fut_2 };

    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, hot_futures, future_wait_us, step_us));
    TEST_ASSERT_TRUE(e2e::wait_all_futures(net, now, cold_futures, future_wait_us, step_us));
    e2e::drive_for(net, now, 200'000, step_us);

    TEST_ASSERT_EQUAL_size_t(0U, hot_capture.malformed);
    TEST_ASSERT_EQUAL_size_t(0U, cold_capture.malformed);
    assert_unordered_complete_unique(hot_capture, hot_pub_id, 1U, 2U);
    assert_unordered_complete_unique(cold_capture, cold_pub_id, 2U, 2U);
    assert_ordered_strictly_increasing(hot_capture, hot_pub_id);
    assert_ordered_strictly_increasing(cold_capture, cold_pub_id);
    assert_unordered_unique_only(hot_capture, hot_pub_id);
    assert_unordered_unique_only(cold_capture, cold_pub_id);
    e2e::assert_future_error(hot_futures, CY_OK);
    e2e::assert_future_error(cold_futures, CY_OK);

    std::vector<cy_future_t*> all_futures = hot_futures;
    all_futures.insert(all_futures.end(), cold_futures.begin(), cold_futures.end());
    e2e::cleanup_case(net, now, all_futures, { hot_sub, cold_sub }, { hot_pub, cold_pub }, step_us, 50'000, 50'000U);
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
    RUN_TEST(test_api_pubsub_e2e_c01_ack_loss_retransmit_duplicate_rejected_unordered);
    RUN_TEST(test_api_pubsub_e2e_c02_ack_loss_retransmit_duplicate_rejected_ordered);
    RUN_TEST(test_api_pubsub_e2e_c03_retransmit_overtakes_newer_message_unordered_unique);
    RUN_TEST(test_api_pubsub_e2e_c04_retransmit_overtakes_newer_message_ordered_restored);
    RUN_TEST(test_api_pubsub_e2e_c05_ordered_gap_timeout_flush);
    RUN_TEST(test_api_pubsub_e2e_c06_late_older_frame_after_timeout_rejected);
    RUN_TEST(test_api_pubsub_e2e_c07_ordered_buffer_capacity_stress_large_jump_backfill);
    RUN_TEST(test_api_pubsub_e2e_c08_high_jitter_moderate_loss_ordered_monotonicity);
    RUN_TEST(test_api_pubsub_e2e_c09_high_jitter_moderate_loss_unordered_completeness);
    RUN_TEST(test_api_pubsub_e2e_c10_reordering_window_boundary_behavior);
    return UNITY_END();
}
