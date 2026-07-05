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

// Regression for H5: a pinned subject (sid <= 8191) published best-effort must not be forced onto the
// headerless v1.0 13-bit plane when the topic name does not hash to rapidhash(decimal(sid)). Such a topic
// (here "foo/bar#611", hash = rapidhash("foo/bar")) would otherwise be silently dropped, because the RX
// fabricates hash = rapidhash("611") and misses. It must take the v1.1 16-bit plane (full header on wire)
// and be delivered. Pre-fix this fails at spin_until_done (the message never arrives).
static void test_api_can_pubsub_pinned_best_effort_custom_name_uses_v11_plane(void)
{
    const uint8_t payload[] = { 0x11U, 0x22U, 0x33U };

    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    node.self_loopback = true;
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "pubsub_pinned_custom");

    cy_future_t* const    sub = cy_subscribe(node.cy, cy_str("foo/bar#611"), 64U);
    cy_publisher_t* const pub = cy_advertise(node.cy, cy_str("foo/bar#611"));
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_NOT_NULL(pub);
    can_test_spin_pair(&node, NULL, 4U, spin_slice_us);
    can_test_node_reset_history(&node);

    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(node.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL }));
    spin_until_done(&node, sub);

    // The 16-bit plane carries the 24-byte Cy header, so a classic-CAN publish spans more than one frame;
    // the headerless 13-bit plane would fit this payload in a single frame.
    TEST_ASSERT_TRUE(node.tx_history_count > 1U);

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

// H5 acceptance criterion: multi-tenant pinned topics sharing one subject-ID (`foo#1234` + `bar#1234`,
// hashes rapidhash("foo")/rapidhash("bar")) must each be delivered best-effort to the matching subscriber
// and filtered correctly. Both are custom-named, so both take the v1.1 16-bit plane and coexist on one
// shared per-subject-ID writer/reader. Pre-fix both were forced onto the 13-bit plane, where RX fabricates
// rapidhash("1234") — matching neither topic — so both were silently dropped.
static void test_api_can_pubsub_multitenant_pinned_best_effort_delivers_and_filters(void)
{
    const uint8_t payload_foo[] = { 0xF0U, 0x0FU, 0xF0U };
    const uint8_t payload_bar[] = { 0xBAU, 0x11U };

    can_test_bus_t  bus;
    can_test_node_t node;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    node.self_loopback = true;
    can_test_node_make_platform(&node, 256U, 0U);
    can_test_node_make_cy(&node, "pubsub_multitenant");

    cy_future_t* const    sub_foo = cy_subscribe(node.cy, cy_str("foo#1234"), 64U);
    cy_future_t* const    sub_bar = cy_subscribe(node.cy, cy_str("bar#1234"), 64U);
    cy_publisher_t* const pub_foo = cy_advertise(node.cy, cy_str("foo#1234"));
    cy_publisher_t* const pub_bar = cy_advertise(node.cy, cy_str("bar#1234"));
    TEST_ASSERT_NOT_NULL(sub_foo);
    TEST_ASSERT_NOT_NULL(sub_bar);
    TEST_ASSERT_NOT_NULL(pub_foo); // both pinned topics coexist on the one shared subject-ID
    TEST_ASSERT_NOT_NULL(pub_bar);
    can_test_spin_pair(&node, NULL, 4U, spin_slice_us);
    can_test_node_reset_history(&node);

    const cy_us_t deadline = cy_now(node.cy) + (20 * spin_slice_us);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub_foo, deadline, (cy_bytes_t){ sizeof(payload_foo), payload_foo, NULL }));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub_bar, deadline, (cy_bytes_t){ sizeof(payload_bar), payload_bar, NULL }));
    spin_until_done(&node, sub_foo);
    spin_until_done(&node, sub_bar);

    // Each subscriber receives EXACTLY its own topic's message and nothing else (hash-filtered on the shared
    // subject-ID): a cross-topic leak would push the other subscriber's arrival count above one. Checking the
    // count (not just the last payload) is required because the future latches only the most recent arrival.
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub_foo));
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub_bar));
    {
        const cy_arrival_t arrival = cy_arrival_move(sub_foo);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, payload_foo, sizeof(payload_foo));
        cy_message_refcount_dec(arrival.message.content);
    }
    {
        const cy_arrival_t arrival = cy_arrival_move(sub_bar);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, payload_bar, sizeof(payload_bar));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(pub_foo);
    cy_unadvertise(pub_bar);
    cy_future_destroy(sub_foo);
    cy_future_destroy(sub_bar);
    can_test_node_spin(&node, spin_slice_us);
    can_test_node_destroy(&node);
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
    const cy_us_t deadline = cy_now(node.cy) + (40 * spin_slice_us);

    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, deadline, (cy_bytes_t){ sizeof(payload), payload, NULL }));
    spin_until_done(&node, sub);
    TEST_ASSERT_TRUE(node.tx_fd_calls > 0U);
    TEST_ASSERT_EQUAL_INT64(deadline, node.last_tx_fd_deadline);

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
    const cy_us_t deadline = cy_now(node.cy) + (40 * spin_slice_us);

    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, deadline, (cy_bytes_t){ sizeof(payload), payload, NULL }));
    spin_until_done(&node, sub);
    TEST_ASSERT_EQUAL_size_t(0U, node.tx_fd_calls);
    TEST_ASSERT_TRUE(node.tx_classic_calls > 0U);
    TEST_ASSERT_EQUAL_INT64(deadline, node.last_tx_classic_deadline);

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
    RUN_TEST(test_api_can_pubsub_pinned_best_effort_custom_name_uses_v11_plane);
    RUN_TEST(test_api_can_pubsub_multitenant_pinned_best_effort_delivers_and_filters);
    RUN_TEST(test_api_can_pubsub_multiframe_extent_truncation);
    RUN_TEST(test_api_can_pubsub_fd_capable_uses_fd_frames);
    RUN_TEST(test_api_can_pubsub_classic_only_emits_no_fd_frames);
    return UNITY_END();
}
