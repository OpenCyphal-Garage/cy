#include "test_support.h"
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

static const cy_us_t spin_slice_us = (cy_us_t)10000;

static void test_api_can_failures_constructor_oom(void)
{
    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, true);
    can_test_heap_fail_after(&node.heap, 0U);
    TEST_ASSERT_NULL(cy_can_new(1U, 32U, 4U, &node.vtable, &node));
    can_test_heap_allow_all(&node.heap);
    can_test_node_destroy(&node);
}

static void test_api_can_failures_subscribe_oom(void)
{
    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    can_test_node_make_platform(&node, 64U, 0U);
    can_test_node_make_cy(&node, "fail_subscribe");

    can_test_heap_fail_after(&node.heap, 0U);
    TEST_ASSERT_NULL(cy_subscribe(node.cy, cy_str("400#400"), 64U));
    can_test_heap_allow_all(&node.heap);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

static void test_api_can_failures_receive_wrapper_oom_drops_message_without_leak(void)
{
    const uint8_t payload[] = { 0x71U, 0x72U, 0x73U, 0x74U };

    can_test_bus_t  bus;
    can_test_node_t a;
    can_test_node_t b;
    can_test_bus_init(&bus);
    can_test_node_prepare(&a, &bus, 1U, false, false);
    can_test_node_prepare(&b, &bus, 1U, false, false);
    can_test_node_make_platform(&a, 128U, 0U);
    can_test_node_make_platform(&b, 128U, 0U);
    can_test_node_make_cy(&a, "fail_rx_a");
    can_test_node_make_cy(&b, "fail_rx_b");

    cy_publisher_t* const pub = cy_advertise(a.cy, cy_str("401#401"));
    cy_future_t* const    sub = cy_subscribe(b.cy, cy_str("401#401"), 64U);
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);

    can_test_heap_fail_after(&b.heap, 0U);
    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(a.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
    can_test_spin_pair(&a, &b, 12U, spin_slice_us);
    TEST_ASSERT_FALSE(cy_future_done(sub));

    can_test_heap_allow_all(&b.heap);
    cy_unadvertise(pub);
    cy_future_destroy(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);
    can_test_node_destroy(&a);
    can_test_node_destroy(&b);
}

static void test_api_can_failures_tx_queue_capacity_is_reported(void)
{
    uint8_t payload[48];
    bool    saw_capacity = false;

    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    can_test_node_make_platform(&node, 1U, 0U);
    can_test_node_make_cy(&node, "fail_capacity");
    can_test_fill_payload(payload, sizeof(payload), 0x80U);

    cy_publisher_t* const pub = cy_advertise(node.cy, cy_str("402#402"));
    TEST_ASSERT_NOT_NULL(pub);

    for (size_t i = 0U; i < 8U; i++) {
        const cy_err_t err =
          cy_publish(pub, cy_now(node.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL });
        if (err == CY_ERR_CAPACITY) {
            saw_capacity = true;
            break;
        }
    }
    TEST_ASSERT_TRUE(saw_capacity);

    cy_unadvertise(pub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_failures_constructor_oom);
    RUN_TEST(test_api_can_failures_subscribe_oom);
    RUN_TEST(test_api_can_failures_receive_wrapper_oom_drops_message_without_leak);
    RUN_TEST(test_api_can_failures_tx_queue_capacity_is_reported);
    return UNITY_END();
}
