#include "test_support.h"
#include <canard.h>
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

static const cy_us_t spin_slice_us = (cy_us_t)10000;

typedef struct
{
    size_t        count;
    cy_us_t       timestamp;
    cy_prio_t     priority;
    uint_least8_t source_node_id;
    uint_least8_t transfer_id;
    size_t        payload_size;
    bool          next_is_null;
    uint8_t       payload[256];
} v0_capture_t;

typedef struct
{
    cy_platform_t* platform;
    cy_t*          cy;
    size_t         count;
    cy_err_t       publish_error;
} v0_publish_from_callback_t;

typedef struct
{
    const v0_capture_t* capture;
    size_t              count;
} capture_goal_t;

static size_t count_topics(const cy_t* const cy)
{
    size_t out = 0U;
    for (cy_topic_t* topic = cy_topic_iter_first(cy); topic != NULL; topic = cy_topic_iter_next(topic)) {
        out++;
    }
    return out;
}

static bool capture_goal_reached(void* const context)
{
    const capture_goal_t* const goal = (const capture_goal_t*)context;
    return (goal->capture != NULL) && (goal->capture->count >= goal->count);
}

static uint16_t transfer_crc(uint16_t crc, const uint8_t* const data, const size_t size)
{
    for (size_t i = 0U; i < size; i++) {
        crc = (uint16_t)(crc ^ (uint16_t)((uint16_t)data[i] << 8U));
        for (size_t bit = 0U; bit < 8U; bit++) {
            const uint16_t shifted = (uint16_t)(crc << 1U);
            crc                    = ((crc & 0x8000U) != 0U) ? (uint16_t)(shifted ^ 0x1021U) : shifted;
        }
    }
    return crc;
}

static void push_rx_frame(can_test_node_t* const node,
                          const uint32_t         can_id,
                          const cy_us_t          timestamp,
                          const uint8_t* const   payload,
                          const size_t           payload_size,
                          const uint8_t          tail)
{
    cy_can_rx_t frame = { .timestamp = timestamp, .can_id = can_id };
    TEST_ASSERT_TRUE(payload_size < sizeof(frame.data));
    frame.len = (uint_least8_t)(payload_size + 1U);
    if (payload_size > 0U) {
        (void)memcpy(frame.data, payload, payload_size);
    }
    frame.data[payload_size] = tail;
    can_test_node_push_rx(node, &frame);
}

static void spin_until_capture(can_test_node_t* const    a,
                               can_test_node_t* const    b,
                               const v0_capture_t* const capture,
                               const size_t              count,
                               const size_t              rounds)
{
    const capture_goal_t goal = { .capture = capture, .count = count };
    TEST_ASSERT_TRUE(
      can_test_spin_pair_until_condition(a, b, capture_goal_reached, (void*)&goal, rounds, spin_slice_us));
}

static void spin_until_done(can_test_node_t* const a, can_test_node_t* const b, cy_future_t* const future)
{
    TEST_ASSERT_NOT_NULL(future);
    TEST_ASSERT_TRUE(can_test_spin_pair_until_future_done(a, b, future, 128U, spin_slice_us));
    TEST_ASSERT_TRUE(cy_future_done(future));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(future));
}

static void on_v0_transfer(cy_can_v0_subscription_t* const subscription,
                           const cy_us_t                   timestamp,
                           const cy_prio_t                 priority,
                           const uint_least8_t             source_node_id,
                           const uint_least8_t             transfer_id,
                           const cy_bytes_t                payload)
{
    TEST_ASSERT_NOT_NULL(subscription);
    v0_capture_t* const capture = (v0_capture_t*)cy_can_v0_subscription_context(subscription).ptr[0];
    TEST_ASSERT_NOT_NULL(capture);
    TEST_ASSERT_TRUE(payload.size <= sizeof(capture->payload));
    capture->count++;
    capture->timestamp      = timestamp;
    capture->priority       = priority;
    capture->source_node_id = source_node_id;
    capture->transfer_id    = transfer_id;
    capture->payload_size   = payload.size;
    capture->next_is_null   = payload.next == NULL;
    if (payload.size > 0U) {
        (void)memcpy(capture->payload, payload.data, payload.size);
    }
}

static void on_v0_transfer_publish(cy_can_v0_subscription_t* const subscription,
                                   const cy_us_t                   timestamp,
                                   const cy_prio_t                 priority,
                                   const uint_least8_t             source_node_id,
                                   const uint_least8_t             transfer_id,
                                   const cy_bytes_t                payload)
{
    static const uint8_t              response[] = { 0xA5U, 0x5AU };
    v0_publish_from_callback_t* const state =
      (v0_publish_from_callback_t*)cy_can_v0_subscription_context(subscription).ptr[0];
    (void)timestamp;
    (void)priority;
    (void)source_node_id;
    (void)transfer_id;
    (void)payload;
    TEST_ASSERT_NOT_NULL(state);
    state->count++;
    state->publish_error = cy_can_v0_publish(state->platform,
                                             cy_now(state->cy) + spin_slice_us,
                                             cy_prio_high,
                                             902U,
                                             0U,
                                             0U,
                                             (cy_bytes_t){ .size = sizeof(response), .data = response, .next = NULL });
}

static void test_api_can_v0_single_frame_no_topic_side_effects_and_cy_coexistence(void)
{
    static const uint8_t v0_payload[] = { 0x11U, 0x22U, 0x33U, 0x44U, 0x55U };
    static const uint8_t cy_payload[] = { 0xA1U, 0xB2U, 0xC3U, 0xD4U };

    can_test_bus_t  bus;
    can_test_node_t tx_node;
    can_test_node_t rx_node;
    v0_capture_t    capture = { 0 };
    can_test_bus_init(&bus);
    can_test_node_prepare(&tx_node, &bus, 1U, true, false);
    can_test_node_prepare(&rx_node, &bus, 1U, true, false);
    can_test_node_make_platform(&tx_node, 256U, 0U);
    can_test_node_make_platform(&rx_node, 256U, 0U);
    can_test_node_make_cy(&tx_node, "v0_tx");
    can_test_node_make_cy(&rx_node, "v0_rx");

    TEST_ASSERT_EQUAL_size_t(0U, count_topics(tx_node.cy));
    TEST_ASSERT_EQUAL_size_t(0U, count_topics(rx_node.cy));

    cy_can_v0_subscription_t* const v0_sub = cy_can_v0_subscribe(rx_node.platform, 341U, 0xBADC, 64U, 500000U);
    TEST_ASSERT_NOT_NULL(v0_sub);
    cy_can_v0_subscription_context_set(v0_sub, (cy_user_context_t){ .ptr = { &capture, NULL } });
    cy_can_v0_subscription_callback_set(v0_sub, on_v0_transfer);
    TEST_ASSERT_TRUE(cy_can_v0_subscription_context(v0_sub).ptr[0] == &capture);
    TEST_ASSERT_TRUE(cy_can_v0_subscription_callback(v0_sub) == on_v0_transfer);

    TEST_ASSERT_EQUAL_size_t(0U, count_topics(tx_node.cy));
    TEST_ASSERT_EQUAL_size_t(0U, count_topics(rx_node.cy));

    can_test_node_reset_history(&tx_node);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_can_v0_publish(tx_node.platform,
                                            cy_now(tx_node.cy) + (20 * spin_slice_us),
                                            cy_prio_high,
                                            341U,
                                            0xBADC,
                                            5U,
                                            (cy_bytes_t){ sizeof(v0_payload), v0_payload, NULL }));
    spin_until_capture(&tx_node, &rx_node, &capture, 1U, 64U);
    TEST_ASSERT_EQUAL_size_t(1U, tx_node.tx_classic_calls);
    TEST_ASSERT_EQUAL_size_t(0U, tx_node.tx_fd_calls);
    TEST_ASSERT_EQUAL_size_t(sizeof(v0_payload), capture.payload_size);
    TEST_ASSERT_TRUE(capture.next_is_null);
    TEST_ASSERT_EQUAL_UINT8_ARRAY(v0_payload, capture.payload, sizeof(v0_payload));
    TEST_ASSERT_EQUAL_UINT8(5U, capture.transfer_id);
    TEST_ASSERT_EQUAL_INT(cy_prio_high, capture.priority);
    TEST_ASSERT_TRUE(capture.source_node_id != CANARD_NODE_ID_ANONYMOUS);

    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_can_v0_publish(tx_node.platform,
                                            cy_now(tx_node.cy) + (20 * spin_slice_us),
                                            cy_prio_high,
                                            341U,
                                            0xBADC,
                                            6U,
                                            (cy_bytes_t){ .size = 0U, .data = NULL, .next = NULL }));
    spin_until_capture(&tx_node, &rx_node, &capture, 2U, 64U);
    TEST_ASSERT_EQUAL_size_t(0U, capture.payload_size);
    TEST_ASSERT_EQUAL_UINT8(6U, capture.transfer_id);

    TEST_ASSERT_EQUAL_size_t(0U, count_topics(tx_node.cy));
    TEST_ASSERT_EQUAL_size_t(0U, count_topics(rx_node.cy));

    cy_future_t* const    cy_sub = cy_subscribe(rx_node.cy, cy_str("444#444"), 32U);
    cy_publisher_t* const cy_pub = cy_advertise(tx_node.cy, cy_str("444#444"));
    TEST_ASSERT_NOT_NULL(cy_sub);
    TEST_ASSERT_NOT_NULL(cy_pub);
    can_test_spin_pair(&tx_node, &rx_node, 4U, spin_slice_us);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_publish(cy_pub,
                                     cy_now(tx_node.cy) + (20 * spin_slice_us),
                                     (cy_bytes_t){ sizeof(cy_payload), cy_payload, NULL }));
    spin_until_done(&tx_node, &rx_node, cy_sub);

    {
        const cy_arrival_t arrival = cy_arrival_move(cy_sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, cy_payload, sizeof(cy_payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(cy_pub);
    cy_future_destroy(cy_sub);
    cy_can_v0_unsubscribe(v0_sub);
    can_test_spin_pair(&tx_node, &rx_node, 1U, spin_slice_us);
    can_test_node_destroy(&tx_node);
    can_test_node_destroy(&rx_node);
}

static void test_api_can_v0_multiframe_extent_truncation_uses_classic_frames(void)
{
    uint8_t payload[48];

    can_test_bus_t  bus;
    can_test_node_t tx_node;
    can_test_node_t rx_node;
    v0_capture_t    capture = { 0 };
    can_test_bus_init(&bus);
    can_test_node_prepare(&tx_node, &bus, 1U, true, false);
    can_test_node_prepare(&rx_node, &bus, 1U, true, false);
    can_test_node_make_platform(&tx_node, 256U, 0U);
    can_test_node_make_platform(&rx_node, 256U, 0U);
    can_test_node_make_cy(&tx_node, "v0_multi_tx");
    can_test_node_make_cy(&rx_node, "v0_multi_rx");
    can_test_fill_payload(payload, sizeof(payload), 0x40U);

    const uint16_t crc_seed                = canard_v0_crc_seed_from_data_type_signature(UINT64_C(0x1122334455667788));
    cy_can_v0_subscription_t* const v0_sub = cy_can_v0_subscribe(rx_node.platform, 777U, crc_seed, 23U, 1000000U);
    TEST_ASSERT_NOT_NULL(v0_sub);
    cy_can_v0_subscription_context_set(v0_sub, (cy_user_context_t){ .ptr = { &capture, NULL } });
    cy_can_v0_subscription_callback_set(v0_sub, on_v0_transfer);

    can_test_node_reset_history(&tx_node);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_can_v0_publish(tx_node.platform,
                                            cy_now(tx_node.cy) + (40 * spin_slice_us),
                                            cy_prio_fast,
                                            777U,
                                            crc_seed,
                                            9U,
                                            (cy_bytes_t){ sizeof(payload), payload, NULL }));
    spin_until_capture(&tx_node, &rx_node, &capture, 1U, 128U);

    TEST_ASSERT_TRUE(tx_node.tx_history_count > 1U);
    TEST_ASSERT_TRUE(tx_node.tx_classic_calls > 1U);
    TEST_ASSERT_EQUAL_size_t(0U, tx_node.tx_fd_calls);
    TEST_ASSERT_TRUE(capture.next_is_null);
    TEST_ASSERT_EQUAL_size_t(23U, capture.payload_size);
    TEST_ASSERT_EQUAL_UINT8_ARRAY(payload, capture.payload, 23U);
    TEST_ASSERT_EQUAL_UINT8(9U, capture.transfer_id);
    TEST_ASSERT_EQUAL_INT(cy_prio_fast, capture.priority);

    cy_can_v0_unsubscribe(v0_sub);
    can_test_spin_pair(&tx_node, &rx_node, 1U, spin_slice_us);
    can_test_node_destroy(&tx_node);
    can_test_node_destroy(&rx_node);
}

static void test_api_can_v0_duplicate_subscribe_rejected_and_negative_timeout_defaults(void)
{
    static const uint8_t payload_a[] = { 0x01U, 0x02U, 0x03U };
    static const uint8_t payload_b[] = { 0x04U, 0x05U, 0x06U };

    can_test_bus_t  bus;
    can_test_node_t tx_node;
    can_test_node_t rx_node;
    v0_capture_t    capture = { 0 };
    can_test_bus_init(&bus);
    can_test_node_prepare(&tx_node, &bus, 1U, false, false);
    can_test_node_prepare(&rx_node, &bus, 1U, false, false);
    can_test_node_make_platform(&tx_node, 256U, 0U);
    can_test_node_make_platform(&rx_node, 256U, 0U);
    can_test_node_make_cy(&tx_node, "v0_dup_tx");
    can_test_node_make_cy(&rx_node, "v0_dup_rx");

    cy_can_v0_subscription_t* const v0_sub = cy_can_v0_subscribe(rx_node.platform, 1234U, 0xFFFFU, 64U, -1);
    TEST_ASSERT_NOT_NULL(v0_sub);
    TEST_ASSERT_NULL(cy_can_v0_subscribe(rx_node.platform, 1234U, 0xAAAAU, 64U, -1));
    cy_can_v0_subscription_context_set(v0_sub, (cy_user_context_t){ .ptr = { &capture, NULL } });
    cy_can_v0_subscription_callback_set(v0_sub, on_v0_transfer);

    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_can_v0_publish(tx_node.platform,
                                            cy_now(tx_node.cy) + (20 * spin_slice_us),
                                            cy_prio_nominal,
                                            1234U,
                                            0xFFFFU,
                                            3U,
                                            (cy_bytes_t){ sizeof(payload_a), payload_a, NULL }));
    spin_until_capture(&tx_node, &rx_node, &capture, 1U, 64U);
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);

    can_test_spin_pair(&tx_node, &rx_node, 50U, spin_slice_us);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_can_v0_publish(tx_node.platform,
                                            cy_now(tx_node.cy) + (20 * spin_slice_us),
                                            cy_prio_nominal,
                                            1234U,
                                            0xFFFFU,
                                            3U,
                                            (cy_bytes_t){ sizeof(payload_b), payload_b, NULL }));
    can_test_spin_pair(&tx_node, &rx_node, 32U, spin_slice_us);
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);

    can_test_spin_pair(&tx_node, &rx_node, 220U, spin_slice_us);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_can_v0_publish(tx_node.platform,
                                            cy_now(tx_node.cy) + (20 * spin_slice_us),
                                            cy_prio_nominal,
                                            1234U,
                                            0xFFFFU,
                                            3U,
                                            (cy_bytes_t){ sizeof(payload_b), payload_b, NULL }));
    spin_until_capture(&tx_node, &rx_node, &capture, 2U, 64U);
    TEST_ASSERT_EQUAL_UINT8_ARRAY(payload_b, capture.payload, sizeof(payload_b));

    cy_can_v0_unsubscribe(v0_sub);
    cy_can_v0_subscription_t* const v0_sub_again = cy_can_v0_subscribe(rx_node.platform, 1234U, 0xAAAAU, 64U, -1);
    TEST_ASSERT_NOT_NULL(v0_sub_again);
    cy_can_v0_unsubscribe(v0_sub_again);
    cy_can_v0_subscription_t* const other_sub = cy_can_v0_subscribe(rx_node.platform, 5678U, 0xAAAAU, 64U, -1);
    TEST_ASSERT_NOT_NULL(other_sub);
    cy_can_v0_unsubscribe(other_sub);

    can_test_spin_pair(&tx_node, &rx_node, 1U, spin_slice_us);
    can_test_node_destroy(&tx_node);
    can_test_node_destroy(&rx_node);
}

static void test_api_can_v0_null_callback_is_safe(void)
{
    static const uint8_t payload[] = { 0x21U, 0x22U, 0x23U };

    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    node.self_loopback = true;
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "v0_null_cb");

    cy_can_v0_subscription_t* const v0_sub = cy_can_v0_subscribe(node.platform, 2345U, 0xFFFFU, 64U, -1);
    TEST_ASSERT_NOT_NULL(v0_sub);
    TEST_ASSERT_NULL(cy_can_v0_subscription_callback(v0_sub));

    can_test_node_reset_history(&node);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_can_v0_publish(node.platform,
                                            cy_now(node.cy) + (20 * spin_slice_us),
                                            cy_prio_low,
                                            2345U,
                                            0xFFFFU,
                                            1U,
                                            (cy_bytes_t){ sizeof(payload), payload, NULL }));
    can_test_node_spin(&node, 20 * spin_slice_us);
    TEST_ASSERT_TRUE(node.tx_classic_calls > 0U);

    cy_can_v0_unsubscribe(v0_sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

static void test_api_can_v0_callback_can_publish_and_transmit(void)
{
    static const uint8_t request[] = { 0x13U, 0x37U };

    can_test_bus_t             bus;
    can_test_node_t            node;
    v0_publish_from_callback_t state = { 0 };
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    node.self_loopback = true;
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "v0_publish_callback");

    cy_can_v0_subscription_t* const sub = cy_can_v0_subscribe(node.platform, 901U, 0U, 64U, -1);
    TEST_ASSERT_NOT_NULL(sub);
    state.platform = node.platform;
    state.cy       = node.cy;
    cy_can_v0_subscription_context_set(sub, (cy_user_context_t){ .ptr = { &state, NULL } });
    cy_can_v0_subscription_callback_set(sub, on_v0_transfer_publish);

    can_test_node_reset_history(&node);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_can_v0_publish(node.platform,
                                            cy_now(node.cy) + (20 * spin_slice_us),
                                            cy_prio_nominal,
                                            901U,
                                            0U,
                                            0U,
                                            (cy_bytes_t){ .size = sizeof(request), .data = request, .next = NULL }));
    can_test_node_spin(&node, 20 * spin_slice_us);
    TEST_ASSERT_EQUAL_size_t(1U, state.count);
    TEST_ASSERT_EQUAL_INT(CY_OK, state.publish_error);
    TEST_ASSERT_TRUE(node.tx_classic_calls >= 2U);

    cy_can_v0_unsubscribe(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

static void test_api_can_v0_and_v1_completions_from_same_frame_are_both_delivered(void)
{
    static const uint16_t subject_id   = 321U;
    static const uint8_t  v1_payload[] = { 0x11U, 0x22U, 0x33U, 0x44U, 0x55U, 0x66U, 0x77U };
    static const uint8_t  v0_middle[]  = { 0x81U, 0x82U, 0x83U, 0x84U, 0x85U, 0x86U, 0x87U };
    uint8_t               v0_head[]    = { 0U, 0U, 0x71U, 0x72U, 0x73U, 0x74U, 0x75U };
    uint8_t               shared_end[2];
    uint8_t               v0_expected[14];

    const uint16_t v1_crc = transfer_crc(UINT16_MAX, v1_payload, sizeof(v1_payload));
    shared_end[0]         = (uint8_t)(v1_crc >> 8U);
    shared_end[1]         = (uint8_t)(v1_crc & 0xFFU);
    uint16_t v0_crc       = transfer_crc(UINT16_MAX, &v0_head[2], sizeof(v0_head) - 2U);
    v0_crc                = transfer_crc(v0_crc, v0_middle, sizeof(v0_middle));
    v0_crc                = transfer_crc(v0_crc, shared_end, sizeof(shared_end));
    v0_head[0]            = (uint8_t)(v0_crc & 0xFFU);
    v0_head[1]            = (uint8_t)(v0_crc >> 8U);
    (void)memcpy(v0_expected, &v0_head[2], sizeof(v0_head) - 2U);
    (void)memcpy(&v0_expected[sizeof(v0_head) - 2U], v0_middle, sizeof(v0_middle));
    (void)memcpy(&v0_expected[(sizeof(v0_head) - 2U) + sizeof(v0_middle)], shared_end, sizeof(shared_end));

    can_test_bus_t  bus;
    can_test_node_t node;
    v0_capture_t    capture = { 0 };
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "mixed_v0_v1");

    cy_future_t* const              v1_sub       = cy_subscribe(node.cy, cy_str("321#321"), 64U);
    const uint16_t                  data_type_id = (uint16_t)(0x6000U | (uint32_t)subject_id);
    cy_can_v0_subscription_t* const v0_sub = cy_can_v0_subscribe(node.platform, data_type_id, UINT16_MAX, 64U, -1);
    TEST_ASSERT_NOT_NULL(v1_sub);
    TEST_ASSERT_NOT_NULL(v0_sub);
    cy_can_v0_subscription_context_set(v0_sub, (cy_user_context_t){ .ptr = { &capture, NULL } });
    cy_can_v0_subscription_callback_set(v0_sub, on_v0_transfer);

    const uint32_t can_id =
      ((uint32_t)cy_prio_nominal << 26U) | (UINT32_C(3) << 21U) | ((uint32_t)subject_id << 8U) | UINT32_C(42);
    push_rx_frame(&node, can_id, 1001, v0_head, sizeof(v0_head), UINT8_C(0x80));
    push_rx_frame(&node, can_id, 1002, v1_payload, sizeof(v1_payload), UINT8_C(0xA0));
    push_rx_frame(&node, can_id, 1003, v0_middle, sizeof(v0_middle), UINT8_C(0x20));
    push_rx_frame(&node, can_id, 1004, shared_end, sizeof(shared_end), UINT8_C(0x40));
    can_test_node_spin(&node, spin_slice_us);

    TEST_ASSERT_EQUAL_size_t(1U, capture.count);
    TEST_ASSERT_EQUAL_size_t(sizeof(v0_expected), capture.payload_size);
    TEST_ASSERT_EQUAL_UINT8_ARRAY(v0_expected, capture.payload, sizeof(v0_expected));
    TEST_ASSERT_TRUE(cy_future_done(v1_sub));
    {
        const cy_arrival_t arrival = cy_arrival_move(v1_sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, v1_payload, sizeof(v1_payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_can_v0_unsubscribe(v0_sub);
    cy_future_destroy(v1_sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_v0_single_frame_no_topic_side_effects_and_cy_coexistence);
    RUN_TEST(test_api_can_v0_multiframe_extent_truncation_uses_classic_frames);
    RUN_TEST(test_api_can_v0_duplicate_subscribe_rejected_and_negative_timeout_defaults);
    RUN_TEST(test_api_can_v0_null_callback_is_safe);
    RUN_TEST(test_api_can_v0_callback_can_publish_and_transmit);
    RUN_TEST(test_api_can_v0_and_v1_completions_from_same_frame_are_both_delivered);
    return UNITY_END();
}
