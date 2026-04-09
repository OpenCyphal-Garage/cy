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

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_v0_single_frame_no_topic_side_effects_and_cy_coexistence);
    RUN_TEST(test_api_can_v0_multiframe_extent_truncation_uses_classic_frames);
    RUN_TEST(test_api_can_v0_duplicate_subscribe_rejected_and_negative_timeout_defaults);
    RUN_TEST(test_api_can_v0_null_callback_is_safe);
    return UNITY_END();
}
