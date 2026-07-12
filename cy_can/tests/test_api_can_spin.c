#include "test_support.h"
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

static const cy_us_t spin_slice_us = (cy_us_t)10000;

typedef struct
{
    cy_platform_t* platform;
    cy_t*          cy;
    size_t         count;
    bool           publish;
    cy_err_t       publish_error;
} capture_t;

static void on_transfer(cy_can_v0_subscription_t* const subscription,
                        const cy_us_t                   timestamp,
                        const cy_prio_t                 priority,
                        const uint_least8_t             source_node_id,
                        const uint_least8_t             transfer_id,
                        const cy_bytes_t                payload)
{
    static const uint8_t response[] = { 0xA5U };
    capture_t* const     state      = (capture_t*)cy_can_v0_subscription_context(subscription).ptr[0];
    (void)timestamp;
    (void)priority;
    (void)source_node_id;
    (void)transfer_id;
    (void)payload;
    TEST_ASSERT_NOT_NULL(state);
    state->count++;
    if (state->publish) {
        state->publish_error =
          cy_can_v0_publish(state->platform,
                            cy_now(state->cy) + spin_slice_us,
                            cy_prio_high,
                            902U,
                            0U,
                            0U,
                            (cy_bytes_t){ .size = sizeof(response), .data = response, .next = NULL });
    }
}

static void prepare_pair(can_test_bus_t* const bus, can_test_node_t* const tx, can_test_node_t* const rx)
{
    can_test_bus_init(bus);
    can_test_node_prepare(tx, bus, 1U, false, false);
    can_test_node_prepare(rx, bus, 1U, false, false);
    can_test_node_make_platform(tx, 256U, 0U);
    can_test_node_make_platform(rx, 256U, 0U);
    can_test_node_make_cy(tx, "spin_tx");
    can_test_node_make_cy(rx, "spin_rx");
}

static cy_can_v0_subscription_t* subscribe(can_test_node_t* const node,
                                           const uint16_t         data_type_id,
                                           capture_t* const       capture)
{
    cy_can_v0_subscription_t* const out = cy_can_v0_subscribe(node->platform, data_type_id, 0U, 64U, -1);
    TEST_ASSERT_NOT_NULL(out);
    capture->platform = node->platform;
    capture->cy       = node->cy;
    cy_can_v0_subscription_context_set(out, (cy_user_context_t){ .ptr = { capture, NULL } });
    cy_can_v0_subscription_callback_set(out, on_transfer);
    return out;
}

static void queue(can_test_node_t* const tx,
                  can_test_node_t* const rx,
                  const uint16_t         data_type_id,
                  const size_t           count,
                  const cy_us_t          timestamp)
{
    uint8_t payloads[CAN_TEST_MAX_QUEUE];
    TEST_ASSERT_TRUE(count <= sizeof(payloads));
    for (size_t i = 0U; i < count; i++) {
        payloads[i] = (uint8_t)i;
        TEST_ASSERT_EQUAL_INT(
          CY_OK,
          cy_can_v0_publish(tx->platform,
                            cy_now(tx->cy) + spin_slice_us,
                            cy_prio_nominal,
                            data_type_id,
                            0U,
                            (uint_least8_t)i,
                            (cy_bytes_t){ .size = sizeof(payloads[i]), .data = &payloads[i], .next = NULL }));
    }
    can_test_node_spin(tx, spin_slice_us);
    TEST_ASSERT_EQUAL_size_t(count, rx->rx_count);
    for (size_t i = 0U; i < count; i++) {
        rx->rx_queue[(rx->rx_head + i) % CAN_TEST_MAX_QUEUE].timestamp = timestamp;
    }
}

static void destroy_pair(can_test_node_t* const          tx,
                         can_test_node_t* const          rx,
                         cy_can_v0_subscription_t* const subscription)
{
    cy_can_v0_unsubscribe(subscription);
    can_test_node_spin(rx, spin_slice_us);
    can_test_node_spin(tx, spin_slice_us);
    can_test_node_destroy(tx);
    can_test_node_destroy(rx);
}

static void test_api_can_spin_nonblocking_limit(void)
{
    can_test_bus_t  bus;
    can_test_node_t tx;
    can_test_node_t rx;
    capture_t       capture = { 0 };
    prepare_pair(&bus, &tx, &rx);
    cy_can_v0_subscription_t* const sub = subscribe(&rx, 901U, &capture);
    queue(&tx, &rx, 901U, 5U, rx.now);

    const size_t rx_calls = rx.rx_calls;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(rx.cy));
    TEST_ASSERT_EQUAL_size_t(3U, capture.count);
    TEST_ASSERT_EQUAL_size_t(2U, rx.rx_count);
    TEST_ASSERT_EQUAL_size_t(rx_calls + 3U, rx.rx_calls);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(rx.cy));
    TEST_ASSERT_EQUAL_size_t(5U, capture.count);
    TEST_ASSERT_EQUAL_size_t(0U, rx.rx_count);
    TEST_ASSERT_EQUAL_size_t(rx_calls + 6U, rx.rx_calls);

    destroy_pair(&tx, &rx, sub);
}

static void test_api_can_spin_nonblocking_delivers_first_post_watermark_frame(void)
{
    can_test_bus_t  bus;
    can_test_node_t tx;
    can_test_node_t rx;
    capture_t       capture = { 0 };
    prepare_pair(&bus, &tx, &rx);
    cy_can_v0_subscription_t* const sub = subscribe(&rx, 901U, &capture);
    queue(&tx, &rx, 901U, 3U, rx.now + 1);

    const size_t rx_calls = rx.rx_calls;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(rx.cy));
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);
    TEST_ASSERT_EQUAL_size_t(2U, rx.rx_count);
    TEST_ASSERT_EQUAL_size_t(rx_calls + 1U, rx.rx_calls);
    can_test_node_spin(&rx, spin_slice_us);
    TEST_ASSERT_EQUAL_size_t(3U, capture.count);

    destroy_pair(&tx, &rx, sub);
}

static void test_api_can_spin_nonblocking_empty_rx_once(void)
{
    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "spin_empty");

    const size_t rx_calls = node.rx_calls;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(node.cy));
    TEST_ASSERT_EQUAL_size_t(rx_calls + 1U, node.rx_calls);

    can_test_node_destroy(&node);
}

static void test_api_can_spin_final_poll_transmits_callback_response(void)
{
    can_test_bus_t  bus;
    can_test_node_t tx;
    can_test_node_t rx;
    capture_t       capture = { .publish = true, .publish_error = CY_ERR_ARGUMENT };
    prepare_pair(&bus, &tx, &rx);
    cy_can_v0_subscription_t* const sub = subscribe(&rx, 901U, &capture);
    queue(&tx, &rx, 901U, 1U, rx.now + 1);

    can_test_node_reset_history(&rx);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(rx.cy));
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);
    TEST_ASSERT_EQUAL_INT(CY_OK, capture.publish_error);
    TEST_ASSERT_TRUE(rx.tx_classic_calls > 0U);

    destroy_pair(&tx, &rx, sub);
}

static void test_api_can_spin_blocking_is_not_limited(void)
{
    can_test_bus_t  bus;
    can_test_node_t tx;
    can_test_node_t rx;
    capture_t       capture = { 0 };
    prepare_pair(&bus, &tx, &rx);
    cy_can_v0_subscription_t* const sub = subscribe(&rx, 901U, &capture);
    queue(&tx, &rx, 901U, 5U, rx.now);

    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(rx.cy, cy_now(rx.cy) + spin_slice_us));
    TEST_ASSERT_EQUAL_size_t(5U, capture.count);
    TEST_ASSERT_EQUAL_size_t(0U, rx.rx_count);

    destroy_pair(&tx, &rx, sub);
}

static void test_api_can_spin_blocking_delivers_first_post_deadline_frame(void)
{
    can_test_bus_t  bus;
    can_test_node_t tx;
    can_test_node_t rx;
    capture_t       capture = { 0 };
    prepare_pair(&bus, &tx, &rx);
    cy_can_v0_subscription_t* const sub      = subscribe(&rx, 901U, &capture);
    const cy_us_t                   deadline = cy_now(rx.cy) + spin_slice_us;
    queue(&tx, &rx, 901U, 2U, deadline + 1);

    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(rx.cy, deadline));
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);
    TEST_ASSERT_EQUAL_size_t(1U, rx.rx_count);
    can_test_node_spin(&rx, spin_slice_us);
    TEST_ASSERT_EQUAL_size_t(2U, capture.count);

    destroy_pair(&tx, &rx, sub);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_spin_nonblocking_limit);
    RUN_TEST(test_api_can_spin_nonblocking_delivers_first_post_watermark_frame);
    RUN_TEST(test_api_can_spin_nonblocking_empty_rx_once);
    RUN_TEST(test_api_can_spin_final_poll_transmits_callback_response);
    RUN_TEST(test_api_can_spin_blocking_is_not_limited);
    RUN_TEST(test_api_can_spin_blocking_delivers_first_post_deadline_frame);
    return UNITY_END();
}
