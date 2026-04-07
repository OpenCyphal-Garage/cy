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
} response_count_context_t;

static bool is_future_done(void* const context)
{
    const future_done_context_t* const ctx = (const future_done_context_t*)context;
    return (ctx != NULL) && cy_future_done(ctx->future);
}

static bool has_response_count(void* const context)
{
    const response_count_context_t* const ctx = (const response_count_context_t*)context;
    return (ctx != NULL) && (cy_response_count(ctx->future) >= ctx->minimum_count);
}

static void test_api_udp_posix_rpc_request_response_reliable(void)
{
    static const uint8_t request_payload[]  = { 0x10U, 0x20U, 0x30U };
    static const uint8_t response_payload[] = { 0xAAU, 0xBBU, 0xCCU, 0xDDU };
    udp_test_node_t      client_node;
    udp_test_node_t      server_node;
    cy_future_t*         response_delivery = NULL;

    udp_test_node_init_manual(&client_node, UINT64_C(0xB000000000000001), "udp_cli", 256U);
    udp_test_node_init_manual(&server_node, UINT64_C(0xB000000000000002), "udp_srv", 256U);

    cy_publisher_t* const client_pub = cy_advertise_client(client_node.cy, cy_str("udp/rpc"), 64U);
    cy_future_t* const    server_sub = cy_subscribe(server_node.cy, cy_str("udp/rpc"), 64U);
    cy_future_t*          request    = NULL;
    TEST_ASSERT_NOT_NULL(client_pub);
    TEST_ASSERT_NOT_NULL(server_sub);

    udp_test_spin_pair(&client_node, &server_node, 8U, spin_slice_us);
    request = cy_request(client_pub,
                         cy_now(client_node.cy) + (200 * spin_slice_us),
                         50 * spin_slice_us,
                         (cy_bytes_t){ sizeof(request_payload), request_payload, NULL });
    TEST_ASSERT_NOT_NULL(request);
    {
        future_done_context_t ctx = { .future = server_sub };
        TEST_ASSERT_TRUE(
          udp_test_spin_pair_until_condition(&client_node, &server_node, is_future_done, &ctx, 120U, spin_slice_us));
    }

    {
        const cy_arrival_t arrival    = cy_arrival_move(server_sub);
        cy_breadcrumb_t    breadcrumb = arrival.breadcrumb;
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        udp_test_assert_message_equals(arrival.message.content, request_payload, sizeof(request_payload));
        response_delivery = cy_respond_reliable(&breadcrumb,
                                                cy_now(server_node.cy) + (200 * spin_slice_us),
                                                (cy_bytes_t){ sizeof(response_payload), response_payload, NULL });
        TEST_ASSERT_NOT_NULL(response_delivery);
        cy_message_refcount_dec(arrival.message.content);
    }

    {
        response_count_context_t ctx = { .future = request, .minimum_count = 1U };
        TEST_ASSERT_TRUE(udp_test_spin_pair_until_condition(
          &client_node, &server_node, has_response_count, &ctx, 200U, spin_slice_us));
    }
    TEST_ASSERT_TRUE(cy_future_done(request));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(request));
    {
        future_done_context_t ctx = { .future = response_delivery };
        TEST_ASSERT_TRUE(
          udp_test_spin_pair_until_condition(&client_node, &server_node, is_future_done, &ctx, 120U, spin_slice_us));
    }
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(response_delivery));

    {
        const cy_response_t response = cy_response_move(request);
        TEST_ASSERT_NOT_NULL(response.message.content);
        TEST_ASSERT_EQUAL_UINT64(server_node.uid, response.remote_id);
        udp_test_assert_message_equals(response.message.content, response_payload, sizeof(response_payload));
        cy_message_refcount_dec(response.message.content);
    }

    cy_future_destroy(response_delivery);
    cy_future_destroy(request);
    cy_unadvertise(client_pub);
    cy_future_destroy(server_sub);
    udp_test_spin_pair(&client_node, &server_node, 6U, spin_slice_us);

    udp_test_node_deinit(&client_node);
    udp_test_node_deinit(&server_node);
}

static void test_api_udp_posix_lifecycle_subscriber_recreation_before_spin(void)
{
    static const uint8_t payload[] = { 0x51U, 0x52U, 0x53U, 0x54U };
    udp_test_node_t      a;
    udp_test_node_t      b;

    udp_test_node_init_manual(&a, UINT64_C(0xB000000000000011), "udp_life_a", 256U);
    udp_test_node_init_manual(&b, UINT64_C(0xB000000000000012), "udp_life_b", 256U);

    cy_publisher_t* const pub     = cy_advertise(a.cy, cy_str("udp/revive"));
    cy_future_t*          old_sub = cy_subscribe(b.cy, cy_str("udp/revive"), 64U);
    cy_future_t*          new_sub = NULL;
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(old_sub);

    cy_future_destroy(old_sub);
    old_sub = NULL;
    new_sub = cy_subscribe(b.cy, cy_str("udp/revive"), 64U);
    TEST_ASSERT_NOT_NULL(new_sub);

    udp_test_spin_pair(&a, &b, 8U, spin_slice_us);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_publish(pub, cy_now(a.cy) + (50 * spin_slice_us), (cy_bytes_t){ 4U, payload, NULL }));

    {
        future_done_context_t ctx = { .future = new_sub };
        TEST_ASSERT_TRUE(udp_test_spin_pair_until_condition(&a, &b, is_future_done, &ctx, 120U, spin_slice_us));
    }

    {
        const cy_arrival_t arrival = cy_arrival_move(new_sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        udp_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_unadvertise(pub);
    cy_future_destroy(new_sub);
    udp_test_spin_pair(&a, &b, 6U, spin_slice_us);

    udp_test_node_deinit(&a);
    udp_test_node_deinit(&b);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_udp_posix_rpc_request_response_reliable);
    RUN_TEST(test_api_udp_posix_lifecycle_subscriber_recreation_before_spin);
    return UNITY_END();
}
