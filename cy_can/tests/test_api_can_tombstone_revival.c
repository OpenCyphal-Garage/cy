#include "test_support.h"
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

static const cy_us_t spin_slice_us = (cy_us_t)10000;

typedef struct
{
    can_test_bus_t  bus;
    can_test_node_t node;
} fixture_t;

static void fixture_init(fixture_t* const self, const char* const home)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_NOT_NULL(home);
    can_test_bus_init(&self->bus);
    can_test_node_prepare(&self->node, &self->bus, 1U, false, true);
    self->node.self_loopback = true;
    can_test_node_make_platform(&self->node, 256U, 16U);
    can_test_node_make_cy(&self->node, home);
}

static void fixture_deinit(fixture_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    can_test_node_destroy(&self->node);
}

static size_t settle_filters(can_test_node_t* const node)
{
    TEST_ASSERT_NOT_NULL(node);
    can_test_node_spin(node, spin_slice_us);
    can_test_node_spin(node, spin_slice_us);
    {
        const size_t out = node->filter_calls;
        can_test_node_spin(node, spin_slice_us);
        TEST_ASSERT_EQUAL_size_t(out, node->filter_calls);
        return out;
    }
}

static void spin_until_done(can_test_node_t* const node, cy_future_t* const future)
{
    TEST_ASSERT_NOT_NULL(node);
    TEST_ASSERT_NOT_NULL(future);
    for (size_t i = 0U; (i < 80U) && !cy_future_done(future); i++) {
        can_test_node_spin(node, spin_slice_us);
    }
    TEST_ASSERT_TRUE(cy_future_done(future));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(future));
}

static void publish_and_expect_payload(can_test_node_t* const node,
                                       cy_future_t* const     sub,
                                       const char* const      topic_name,
                                       const void* const      payload,
                                       const size_t           size)
{
    cy_publisher_t* const pub = cy_advertise(node->cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(node->cy) + (20 * spin_slice_us), (cy_bytes_t){ size, payload, NULL }));
    spin_until_done(node, sub);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub));
    {
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        TEST_ASSERT_EQUAL_size_t(size, cy_message_size(arrival.message.content));
        can_test_assert_message_equals(arrival.message.content, payload, size);
        cy_message_refcount_dec(arrival.message.content);
    }
    cy_unadvertise(pub);
}

static void run_revive_extent_case(const char* const topic_name,
                                   const char* const home,
                                   const size_t      first_extent,
                                   const size_t      second_extent)
{
    uint8_t   payload[96];
    fixture_t fix;
    size_t    baseline_filter_calls = 0U;
    can_test_fill_payload(payload, sizeof(payload), 0x30U);
    fixture_init(&fix, home);

    cy_future_t* const first = cy_subscribe(fix.node.cy, cy_str(topic_name), first_extent);
    TEST_ASSERT_NOT_NULL(first);
    baseline_filter_calls = settle_filters(&fix.node);

    cy_future_destroy(first);
    {
        cy_future_t* const second = cy_subscribe(fix.node.cy, cy_str(topic_name), second_extent);
        TEST_ASSERT_NOT_NULL(second);
        TEST_ASSERT_EQUAL_size_t(baseline_filter_calls, settle_filters(&fix.node));
        publish_and_expect_payload(&fix.node, second, topic_name, payload, sizeof(payload));
        cy_future_destroy(second);
    }

    can_test_node_spin(&fix.node, spin_slice_us);
    fixture_deinit(&fix);
}

static void test_api_can_tombstone_verbatim_revive_preserves_old_larger_extent(void)
{
    run_revive_extent_case("tombstone/verbatim_preserve", "tombstone_verbatim_preserve", 128U, 64U);
}

static void test_api_can_tombstone_verbatim_revive_grows_extent(void)
{
    run_revive_extent_case("tombstone/verbatim_grow", "tombstone_verbatim_grow", 64U, 128U);
}

static void test_api_can_tombstone_pinned_revive_preserves_old_larger_extent(void)
{
    run_revive_extent_case("123#123", "tombstone_pinned_preserve", 128U, 64U);
}

static void test_api_can_tombstone_pinned_revive_grows_extent(void)
{
    run_revive_extent_case("124#124", "tombstone_pinned_grow", 64U, 128U);
}

static void test_api_can_tombstone_recreate_after_spin_reconfigures_filters(void)
{
    const uint8_t payload[] = { 0x41U, 0x42U, 0x43U, 0x44U };
    fixture_t     fix;
    size_t        before_destroy = 0U;
    size_t        after_destroy  = 0U;
    fixture_init(&fix, "tombstone_recreate_after_spin");

    cy_future_t* first = cy_subscribe(fix.node.cy, cy_str("125#125"), 64U);
    TEST_ASSERT_NOT_NULL(first);
    before_destroy = settle_filters(&fix.node);

    cy_future_destroy(first);
    after_destroy = settle_filters(&fix.node);
    TEST_ASSERT_TRUE(after_destroy > before_destroy);

    {
        cy_future_t* const second = cy_subscribe(fix.node.cy, cy_str("125#125"), 64U);
        TEST_ASSERT_NOT_NULL(second);
        TEST_ASSERT_TRUE(settle_filters(&fix.node) > after_destroy);
        publish_and_expect_payload(&fix.node, second, "125#125", payload, sizeof(payload));
        cy_future_destroy(second);
    }

    can_test_node_spin(&fix.node, spin_slice_us);
    fixture_deinit(&fix);
}

static void test_api_can_tombstone_multiple_destroy_recreate_cycles_before_spin(void)
{
    const uint8_t payload[] = { 0x51U, 0x52U, 0x53U, 0x54U, 0x55U };
    fixture_t     fix;
    size_t        baseline_filter_calls = 0U;
    fixture_init(&fix, "tombstone_multi_cycle");

    cy_future_t* first = cy_subscribe(fix.node.cy, cy_str("126#126"), 96U);
    TEST_ASSERT_NOT_NULL(first);
    baseline_filter_calls = settle_filters(&fix.node);

    cy_future_destroy(first);
    {
        cy_future_t* const second = cy_subscribe(fix.node.cy, cy_str("126#126"), 64U);
        TEST_ASSERT_NOT_NULL(second);
        cy_future_destroy(second);
    }
    {
        cy_future_t* const third = cy_subscribe(fix.node.cy, cy_str("126#126"), 96U);
        TEST_ASSERT_NOT_NULL(third);
        TEST_ASSERT_EQUAL_size_t(baseline_filter_calls, settle_filters(&fix.node));
        publish_and_expect_payload(&fix.node, third, "126#126", payload, sizeof(payload));
        cy_future_destroy(third);
    }

    can_test_node_spin(&fix.node, spin_slice_us);
    fixture_deinit(&fix);
}

static void test_api_can_tombstone_broadcast_reader_revives_across_cy_recreation(void)
{
    const uint8_t payload[] = { 0x61U, 0x62U, 0x63U };
    fixture_t     fix;
    size_t        baseline_filter_calls = 0U;
    fixture_init(&fix, "tombstone_broadcast_a");
    baseline_filter_calls = settle_filters(&fix.node);

    cy_destroy(fix.node.cy);
    fix.node.cy = NULL;
    can_test_node_make_cy(&fix.node, "tombstone_broadcast_b");
    TEST_ASSERT_EQUAL_size_t(baseline_filter_calls, settle_filters(&fix.node));

    {
        cy_future_t* const sub = cy_subscribe(fix.node.cy, cy_str("127#127"), 64U);
        TEST_ASSERT_NOT_NULL(sub);
        publish_and_expect_payload(&fix.node, sub, "127#127", payload, sizeof(payload));
        cy_future_destroy(sub);
    }

    can_test_node_spin(&fix.node, spin_slice_us);
    fixture_deinit(&fix);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_tombstone_verbatim_revive_preserves_old_larger_extent);
    RUN_TEST(test_api_can_tombstone_verbatim_revive_grows_extent);
    RUN_TEST(test_api_can_tombstone_pinned_revive_preserves_old_larger_extent);
    RUN_TEST(test_api_can_tombstone_pinned_revive_grows_extent);
    RUN_TEST(test_api_can_tombstone_recreate_after_spin_reconfigures_filters);
    RUN_TEST(test_api_can_tombstone_multiple_destroy_recreate_cycles_before_spin);
    RUN_TEST(test_api_can_tombstone_broadcast_reader_revives_across_cy_recreation);
    return UNITY_END();
}
