#include "test_support.h"
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

static const cy_us_t spin_slice_us = (cy_us_t)10000;

static void spin_until_done(can_test_node_t* const node, cy_future_t* const future)
{
    TEST_ASSERT_NOT_NULL(node);
    TEST_ASSERT_NOT_NULL(future);
    for (size_t i = 0U; (i < 64U) && !cy_future_done(future); i++) {
        can_test_node_spin(node, spin_slice_us);
    }
    TEST_ASSERT_TRUE(cy_future_done(future));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(future));
}

static void test_api_can_pubsub_pinned_best_effort_uses_shorter_legacy_path(void)
{
    const uint8_t payload[]       = { 0x11U, 0x22U, 0x33U };
    size_t        verbatim_frames = 0U;
    size_t        pinned_frames   = 0U;

    {
        can_test_bus_t  bus;
        can_test_node_t node;
        can_test_bus_init(&bus);
        can_test_node_prepare(&node, &bus, 1U, false, false);
        node.self_loopback = true;
        can_test_node_make_platform(&node, 256U, 0U);
        can_test_node_make_cy(&node, "pubsub_verbatim");

        cy_future_t* const    sub = cy_subscribe(node.cy, cy_str("pubsub/verbatim"), 64U);
        cy_publisher_t* const pub = cy_advertise(node.cy, cy_str("pubsub/verbatim"));
        TEST_ASSERT_NOT_NULL(sub);
        TEST_ASSERT_NOT_NULL(pub);
        can_test_spin_pair(&node, NULL, 4U, spin_slice_us);
        can_test_node_reset_history(&node);

        TEST_ASSERT_EQUAL_INT(
          CY_OK,
          cy_publish(pub, cy_now(node.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
        spin_until_done(&node, sub);
        verbatim_frames = node.tx_history_count;
        TEST_ASSERT_TRUE(verbatim_frames > 1U);

        {
            const cy_arrival_t arrival = cy_arrival_move(sub);
            TEST_ASSERT_NOT_NULL(arrival.message.content);
            can_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
            cy_message_refcount_dec(arrival.message.content);
        }

        cy_unadvertise(pub);
        cy_future_destroy(sub);
        can_test_node_spin(&node, spin_slice_us);
        can_test_node_destroy(&node);
    }

    {
        can_test_bus_t  bus;
        can_test_node_t node;
        can_test_bus_init(&bus);
        can_test_node_prepare(&node, &bus, 1U, false, false);
        node.self_loopback = true;
        can_test_node_make_platform(&node, 256U, 0U);
        can_test_node_make_cy(&node, "pubsub_pinned");

        cy_future_t* const    sub = cy_subscribe(node.cy, cy_str("123#123"), 64U);
        cy_publisher_t* const pub = cy_advertise(node.cy, cy_str("123#123"));
        TEST_ASSERT_NOT_NULL(sub);
        TEST_ASSERT_NOT_NULL(pub);
        can_test_spin_pair(&node, NULL, 4U, spin_slice_us);
        can_test_node_reset_history(&node);

        TEST_ASSERT_EQUAL_INT(
          CY_OK,
          cy_publish(pub, cy_now(node.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
        spin_until_done(&node, sub);
        pinned_frames = node.tx_history_count;
        TEST_ASSERT_EQUAL_size_t(1U, pinned_frames);

        {
            const cy_arrival_t arrival = cy_arrival_move(sub);
            TEST_ASSERT_NOT_NULL(arrival.message.content);
            can_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
            cy_message_refcount_dec(arrival.message.content);
        }

        cy_unadvertise(pub);
        cy_future_destroy(sub);
        can_test_node_spin(&node, spin_slice_us);
        can_test_node_destroy(&node);
    }

    TEST_ASSERT_TRUE(verbatim_frames > pinned_frames);
}

static void test_api_can_pubsub_multiframe_extent_truncation(void)
{
    uint8_t payload[120];

    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    node.self_loopback = true;
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "pubsub_extent");
    can_test_fill_payload(payload, sizeof(payload), 0x40U);

    cy_future_t* const    sub = cy_subscribe(node.cy, cy_str("pubsub/extent"), 40U);
    cy_publisher_t* const pub = cy_advertise(node.cy, cy_str("pubsub/extent"));
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_NOT_NULL(pub);
    can_test_spin_pair(&node, NULL, 4U, spin_slice_us);
    can_test_node_reset_history(&node);

    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(node.cy) + (40 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
    spin_until_done(&node, sub);
    TEST_ASSERT_TRUE(node.tx_history_count > 1U);

    {
        uint8_t            received[64];
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        TEST_ASSERT_EQUAL_size_t(40U, cy_message_size(arrival.message.content));
        TEST_ASSERT_EQUAL_size_t(40U, can_test_message_read_all(arrival.message.content, received, sizeof(received)));
        TEST_ASSERT_EQUAL_UINT8_ARRAY(payload, received, 40U);
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(pub);
    cy_future_destroy(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

static void test_api_can_pubsub_fd_capable_uses_fd_frames(void)
{
    uint8_t payload[20];

    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, true, false);
    node.self_loopback = true;
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "pubsub_fd");
    can_test_fill_payload(payload, sizeof(payload), 0x60U);

    cy_future_t* const    sub = cy_subscribe(node.cy, cy_str("pubsub/fd"), 64U);
    cy_publisher_t* const pub = cy_advertise(node.cy, cy_str("pubsub/fd"));
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_NOT_NULL(pub);
    can_test_spin_pair(&node, NULL, 4U, spin_slice_us);
    can_test_node_reset_history(&node);

    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(node.cy) + (40 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
    spin_until_done(&node, sub);
    TEST_ASSERT_TRUE(node.tx_fd_calls > 0U);

    {
        uint8_t            received[32];
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        TEST_ASSERT_TRUE(cy_message_size(arrival.message.content) >= sizeof(payload));
        TEST_ASSERT_EQUAL_size_t(sizeof(payload),
                                 cy_message_read(arrival.message.content, 0U, sizeof(payload), received));
        TEST_ASSERT_EQUAL_UINT8_ARRAY(payload, received, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(pub);
    cy_future_destroy(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

static void test_api_can_pubsub_classic_only_emits_no_fd_frames(void)
{
    uint8_t payload[48];

    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    node.self_loopback = true;
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "pubsub_classic");
    can_test_fill_payload(payload, sizeof(payload), 0x20U);

    cy_future_t* const    sub = cy_subscribe(node.cy, cy_str("125#125"), 64U);
    cy_publisher_t* const pub = cy_advertise(node.cy, cy_str("125#125"));
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_NOT_NULL(pub);
    can_test_spin_pair(&node, NULL, 4U, spin_slice_us);
    can_test_node_reset_history(&node);

    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(node.cy) + (40 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
    spin_until_done(&node, sub);
    TEST_ASSERT_EQUAL_size_t(0U, node.tx_fd_calls);
    TEST_ASSERT_TRUE(node.tx_classic_calls > 0U);

    {
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(pub);
    cy_future_destroy(sub);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_pubsub_pinned_best_effort_uses_shorter_legacy_path);
    RUN_TEST(test_api_can_pubsub_multiframe_extent_truncation);
    RUN_TEST(test_api_can_pubsub_fd_capable_uses_fd_frames);
    RUN_TEST(test_api_can_pubsub_classic_only_emits_no_fd_frames);
    return UNITY_END();
}
