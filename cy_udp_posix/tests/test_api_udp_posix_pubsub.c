#include "test_support.h"

#include <unity.h>

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

static const cy_us_t spin_slice_us = (cy_us_t)10000;

typedef struct
{
    cy_future_t* future;
} future_done_context_t;

typedef struct
{
    cy_future_t* future;
    uint64_t     minimum_count;
} arrival_count_context_t;

static bool is_future_done(void* const context)
{
    const future_done_context_t* const ctx = (const future_done_context_t*)context;
    return (ctx != NULL) && cy_future_done(ctx->future);
}

static bool has_arrival_count(void* const context)
{
    const arrival_count_context_t* const ctx = (const arrival_count_context_t*)context;
    return (ctx != NULL) && (cy_arrival_count(ctx->future) >= ctx->minimum_count);
}

static void test_api_udp_posix_pubsub_best_effort_and_stats(void)
{
    static const uint8_t payload[] = { 0x11U, 0x22U, 0x33U, 0x44U };
    udp_test_node_t      a;
    udp_test_node_t      b;
    size_t               writer_baseline = 0U;
    size_t               reader_baseline = 0U;

    udp_test_node_init_manual(&a, UINT64_C(0xA000000000000001), "udp_pub_a", 256U);
    udp_test_node_init_manual(&b, UINT64_C(0xA000000000000002), "udp_pub_b", 256U);
    udp_test_spin_pair(&a, &b, 4U, spin_slice_us);
    writer_baseline = cy_udp_posix_stats(a.platform).subject_writer_count;
    reader_baseline = cy_udp_posix_stats(b.platform).subject_reader_count;

    cy_publisher_t* const pub = cy_advertise(a.cy, cy_str("udp/basic"));
    cy_future_t* const    sub = cy_subscribe(b.cy, cy_str("udp/basic"), 64U);
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(sub);

    udp_test_spin_pair(&a, &b, 8U, spin_slice_us);
    TEST_ASSERT_EQUAL_size_t(writer_baseline + 1U, cy_udp_posix_stats(a.platform).subject_writer_count);
    TEST_ASSERT_TRUE(cy_udp_posix_stats(b.platform).subject_reader_count >= (reader_baseline + 1U));

    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_publish(pub, cy_now(a.cy) + (50 * spin_slice_us), (cy_bytes_t){ 4U, payload, NULL }));

    {
        arrival_count_context_t ctx = { .future = sub, .minimum_count = 1U };
        TEST_ASSERT_TRUE(udp_test_spin_pair_until_condition(&a, &b, has_arrival_count, &ctx, 100U, spin_slice_us));
    }

    {
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        udp_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(pub);
    cy_future_destroy(sub);
    udp_test_spin_pair(&a, &b, 6U, spin_slice_us);

    udp_test_node_deinit(&a);
    udp_test_node_deinit(&b);
}

static void test_api_udp_posix_pubsub_large_reliable_delivery(void)
{
    uint8_t               payload[1024];
    udp_test_node_t       a;
    udp_test_node_t       b;
    future_done_context_t delivery_ctx;

    udp_test_fill_payload(payload, sizeof(payload), 0x40U);
    udp_test_node_init_manual(&a, UINT64_C(0xA000000000000011), "udp_rel_a", 512U);
    udp_test_node_init_manual(&b, UINT64_C(0xA000000000000012), "udp_rel_b", 512U);

    cy_publisher_t* const pub      = cy_advertise(a.cy, cy_str("udp/large"));
    cy_future_t* const    sub      = cy_subscribe(b.cy, cy_str("udp/large"), sizeof(payload));
    cy_future_t*          delivery = NULL;
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(sub);

    udp_test_spin_pair(&a, &b, 8U, spin_slice_us);
    delivery =
      cy_publish_reliable(pub, cy_now(a.cy) + (200 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL });
    TEST_ASSERT_NOT_NULL(delivery);
    delivery_ctx.future = delivery;
    TEST_ASSERT_TRUE(udp_test_spin_pair_until_condition(&a, &b, is_future_done, &delivery_ctx, 200U, spin_slice_us));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(delivery));
    TEST_ASSERT_TRUE(cy_arrival_count(sub) > 0U);

    {
        uint8_t            received[sizeof(payload)];
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        TEST_ASSERT_EQUAL_size_t(sizeof(payload), cy_message_size(arrival.message.content));
        TEST_ASSERT_EQUAL_size_t(sizeof(payload),
                                 udp_test_message_read_all(arrival.message.content, received, sizeof(received)));
        TEST_ASSERT_EQUAL_UINT8_ARRAY(payload, received, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_future_destroy(delivery);
    cy_unadvertise(pub);
    cy_future_destroy(sub);
    udp_test_spin_pair(&a, &b, 6U, spin_slice_us);

    udp_test_node_deinit(&a);
    udp_test_node_deinit(&b);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_udp_posix_pubsub_best_effort_and_stats);
    RUN_TEST(test_api_udp_posix_pubsub_large_reliable_delivery);
    return UNITY_END();
}
