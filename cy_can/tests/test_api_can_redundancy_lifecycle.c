#include "test_support.h"
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

static const cy_us_t spin_slice_us = (cy_us_t)10000;

static void spin_until_done(can_test_node_t* const a, can_test_node_t* const b, cy_future_t* const future)
{
    TEST_ASSERT_NOT_NULL(future);
    TEST_ASSERT_TRUE(can_test_spin_pair_until_future_done(a, b, future, 80U, spin_slice_us));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(future));
}

static void test_api_can_redundancy_duplicate_ingress_is_delivered_once(void)
{
    const uint8_t payload[] = { 0x31U, 0x32U, 0x33U, 0x34U };

    can_test_bus_t  bus;
    can_test_node_t a;
    can_test_node_t b;
    can_test_bus_init(&bus);
    can_test_node_prepare(&a, &bus, 2U, false, false);
    can_test_node_prepare(&b, &bus, 2U, false, false);
    can_test_node_make_platform(&a, 256U, 0U);
    can_test_node_make_platform(&b, 256U, 0U);
    can_test_node_make_cy(&a, "redundancy_a");
    can_test_node_make_cy(&b, "redundancy_b");

    cy_publisher_t* const pub = cy_advertise(a.cy, cy_str("300#300"));
    cy_future_t* const    sub = cy_subscribe(b.cy, cy_str("300#300"), 64U);
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);
    can_test_node_reset_history(&a);

    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(a.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
    spin_until_done(&a, &b, sub);
    TEST_ASSERT_TRUE(can_test_node_count_records_on_iface(&a, 0U) > 0U);
    TEST_ASSERT_TRUE(can_test_node_count_records_on_iface(&a, 1U) > 0U);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub));

    {
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(pub);
    cy_future_destroy(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);
    can_test_node_destroy(&a);
    can_test_node_destroy(&b);
}

static void test_api_can_redundancy_retries_backpressured_interface(void)
{
    const uint8_t payload[] = { 0x41U, 0x42U };

    can_test_bus_t  bus;
    can_test_node_t a;
    can_test_node_t b;
    can_test_bus_init(&bus);
    can_test_node_prepare(&a, &bus, 2U, false, false);
    can_test_node_prepare(&b, &bus, 2U, false, false);
    can_test_node_make_platform(&a, 256U, 0U);
    can_test_node_make_platform(&b, 256U, 0U);
    can_test_node_make_cy(&a, "backpressure_a");
    can_test_node_make_cy(&b, "backpressure_b");

    cy_publisher_t* const pub = cy_advertise(a.cy, cy_str("301#301"));
    cy_future_t* const    sub = cy_subscribe(b.cy, cy_str("301#301"), 64U);
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);
    can_test_node_reset_history(&a);
    a.tx_blocked[1] = 1U;

    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(a.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
    can_test_spin_pair(&a, &b, 1U, spin_slice_us);
    TEST_ASSERT_TRUE(can_test_node_count_records_on_iface(&a, 0U) > 0U);
    TEST_ASSERT_EQUAL_size_t(0U, a.tx_blocked[1]);

    can_test_spin_pair(&a, &b, 1U, spin_slice_us);
    TEST_ASSERT_TRUE(can_test_node_count_records_on_iface(&a, 1U) > 0U);
    spin_until_done(&a, &b, sub);

    {
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(pub);
    cy_future_destroy(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);
    can_test_node_destroy(&a);
    can_test_node_destroy(&b);
}

static void run_subscription_revival_case(const char* const topic_name, const char* const home)
{
    const uint8_t payload[] = { 0x51U, 0x52U, 0x53U, 0x54U, 0x55U };

    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    node.self_loopback = true;
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, home);

    cy_future_t* const first  = cy_subscribe(node.cy, cy_str(topic_name), 64U);
    cy_future_t*       second = NULL;
    cy_publisher_t*    pub    = NULL;
    TEST_ASSERT_NOT_NULL(first);
    cy_future_destroy(first);

    second = cy_subscribe(node.cy, cy_str(topic_name), 64U);
    pub    = cy_advertise(node.cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(second);
    TEST_ASSERT_NOT_NULL(pub);

    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(node.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
    for (size_t i = 0U; (i < 80U) && !cy_future_done(second); i++) {
        can_test_node_spin(&node, spin_slice_us);
    }
    TEST_ASSERT_TRUE(cy_future_done(second));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(second));

    {
        const cy_arrival_t arrival = cy_arrival_move(second);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(pub);
    cy_future_destroy(second);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

static void test_api_can_lifecycle_revives_verbatim_and_pinned_subscriptions(void)
{
    run_subscription_revival_case("lifecycle/verbatim", "revive_verbatim");
    run_subscription_revival_case("302#302", "revive_pinned");
}

static void test_api_can_lifecycle_recreates_cy_on_same_platform(void)
{
    const uint8_t payload[] = { 0x61U, 0x62U, 0x63U };

    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    node.self_loopback = true;
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "first_cy");

    {
        cy_future_t* const first = cy_subscribe(node.cy, cy_str("303#303"), 64U);
        TEST_ASSERT_NOT_NULL(first);
        cy_future_destroy(first);
        can_test_node_spin(&node, spin_slice_us);
    }
    cy_destroy(node.cy);
    node.cy = NULL;

    can_test_node_make_cy(&node, "second_cy");
    {
        cy_future_t* const    sub = cy_subscribe(node.cy, cy_str("303#303"), 64U);
        cy_publisher_t* const pub = cy_advertise(node.cy, cy_str("303#303"));
        TEST_ASSERT_NOT_NULL(sub);
        TEST_ASSERT_NOT_NULL(pub);

        TEST_ASSERT_EQUAL_INT(
          CY_OK,
          cy_publish(pub, cy_now(node.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
        for (size_t i = 0U; (i < 80U) && !cy_future_done(sub); i++) {
            can_test_node_spin(&node, spin_slice_us);
        }
        TEST_ASSERT_TRUE(cy_future_done(sub));

        {
            const cy_arrival_t arrival = cy_arrival_move(sub);
            TEST_ASSERT_NOT_NULL(arrival.message.content);
            can_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
            cy_message_refcount_dec(arrival.message.content);
        }

        cy_unadvertise(pub);
        cy_future_destroy(sub);
        can_test_node_spin(&node, spin_slice_us);
    }

    can_test_node_destroy(&node);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_redundancy_duplicate_ingress_is_delivered_once);
    RUN_TEST(test_api_can_redundancy_retries_backpressured_interface);
    RUN_TEST(test_api_can_lifecycle_revives_verbatim_and_pinned_subscriptions);
    RUN_TEST(test_api_can_lifecycle_recreates_cy_on_same_platform);
    return UNITY_END();
}
