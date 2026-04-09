#include "test_support.h"
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

static const cy_us_t spin_slice_us = (cy_us_t)10000;

static void test_api_can_constructor_rejects_invalid_arguments(void)
{
    static const uint64_t prng_seed = UINT64_C(0xC0DEC0DEC0DEC0DE);
    can_test_bus_t        bus;
    can_test_node_t       node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, true);

    TEST_ASSERT_NULL(cy_can_new(0U, 16U, 0U, prng_seed, &node.vtable, &node));
    TEST_ASSERT_NULL(cy_can_new(CANARD_IFACE_COUNT + 1U, 16U, 0U, prng_seed, &node.vtable, &node));
    TEST_ASSERT_NULL(cy_can_new(1U, 16U, 0U, prng_seed, NULL, &node));

    {
        cy_can_vtable_t v = node.vtable;
        v.tx_classic      = NULL;
        TEST_ASSERT_NULL(cy_can_new(1U, 16U, 0U, prng_seed, &v, &node));
    }
    {
        cy_can_vtable_t v = node.vtable;
        v.rx              = NULL;
        TEST_ASSERT_NULL(cy_can_new(1U, 16U, 0U, prng_seed, &v, &node));
    }
    {
        cy_can_vtable_t v = node.vtable;
        v.now             = NULL;
        TEST_ASSERT_NULL(cy_can_new(1U, 16U, 0U, prng_seed, &v, &node));
    }
    {
        cy_can_vtable_t v = node.vtable;
        v.realloc         = NULL;
        TEST_ASSERT_NULL(cy_can_new(1U, 16U, 0U, prng_seed, &v, &node));
    }

    can_test_node_destroy(&node);
}

static void test_api_can_constructor_user_roundtrip_and_destroy(void)
{
    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, true);
    can_test_node_make_platform(&node, 32U, 4U);
    TEST_ASSERT_TRUE(cy_can_user(node.platform) == &node);
    can_test_node_make_cy(&node, "ctor_roundtrip");
    can_test_node_destroy(&node);
}

static void test_api_can_constructor_filtering_disabled_by_zero_count(void)
{
    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, true);
    can_test_node_make_platform(&node, 32U, 0U);
    can_test_node_make_cy(&node, "filter_zero");

    cy_future_t* const sub = cy_subscribe(node.cy, cy_str("111#111"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_spin(&node, spin_slice_us);
    TEST_ASSERT_EQUAL_size_t(0U, node.filter_calls);

    cy_future_destroy(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

static void test_api_can_constructor_filtering_disabled_by_null_callback(void)
{
    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    can_test_node_make_platform(&node, 32U, 4U);
    can_test_node_make_cy(&node, "filter_null");

    cy_future_t* const sub = cy_subscribe(node.cy, cy_str("112#112"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_spin(&node, spin_slice_us);
    TEST_ASSERT_EQUAL_size_t(0U, node.filter_calls);

    cy_future_destroy(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

static void test_api_can_constructor_filtering_enabled_when_callback_and_count_present(void)
{
    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, true);
    can_test_node_make_platform(&node, 32U, 8U);
    can_test_node_make_cy(&node, "filter_enabled");

    cy_future_t* const sub = cy_subscribe(node.cy, cy_str("113#113"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    can_test_node_spin(&node, spin_slice_us);
    TEST_ASSERT_TRUE(node.filter_calls > 0U);
    TEST_ASSERT_TRUE(node.last_filter_count > 0U);

    cy_future_destroy(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

static void test_api_can_constructor_filter_retries_after_failure(void)
{
    can_test_bus_t  bus;
    can_test_node_t node;
    size_t          first_filter_call_count = 0U;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, true);
    can_test_node_make_platform(&node, 32U, 8U);
    can_test_node_make_cy(&node, "filter_retry");

    cy_future_t* const sub = cy_subscribe(node.cy, cy_str("114#114"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    node.filter_failures_remaining = 1U;

    can_test_node_spin(&node, spin_slice_us);
    first_filter_call_count = node.filter_calls;
    TEST_ASSERT_TRUE(first_filter_call_count > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, node.filter_failures_remaining);
    TEST_ASSERT_TRUE(first_filter_call_count >= 2U);

    cy_future_destroy(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_constructor_rejects_invalid_arguments);
    RUN_TEST(test_api_can_constructor_user_roundtrip_and_destroy);
    RUN_TEST(test_api_can_constructor_filtering_disabled_by_zero_count);
    RUN_TEST(test_api_can_constructor_filtering_disabled_by_null_callback);
    RUN_TEST(test_api_can_constructor_filtering_enabled_when_callback_and_count_present);
    RUN_TEST(test_api_can_constructor_filter_retries_after_failure);
    return UNITY_END();
}
