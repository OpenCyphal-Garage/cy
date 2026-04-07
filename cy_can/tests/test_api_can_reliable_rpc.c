#include "test_support.h"
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

static const cy_us_t spin_slice_us = (cy_us_t)10000;

typedef struct
{
    size_t   count;
    size_t   transient_error_count;
    cy_err_t last_error;
    uint64_t remote_id[4];
    uint64_t seqno[4];
    size_t   size[4];
    uint8_t  payload[4][64];
} response_capture_t;

typedef struct
{
    size_t       calls;
    cy_future_t* reliable_future;
    uint8_t      response_a[8];
    uint8_t      response_b[8];
    size_t       response_a_size;
    size_t       response_b_size;
} request_server_t;

static void on_response_capture(cy_future_t* const future)
{
    response_capture_t* const cap = (response_capture_t*)cy_future_context(future).ptr[0];
    TEST_ASSERT_NOT_NULL(cap);
    if (!cy_future_done(future)) {
        cap->transient_error_count++;
        cap->last_error = cy_future_error(future);
        return;
    }
    if (cy_future_error(future) != CY_OK) {
        cap->last_error = cy_future_error(future);
        return;
    }
    {
        const cy_response_t rsp = cy_response_move(future);
        TEST_ASSERT_NOT_NULL(rsp.message.content);
        TEST_ASSERT_TRUE(cap->count < 4U);
        cap->remote_id[cap->count] = rsp.remote_id;
        cap->seqno[cap->count]     = rsp.seqno;
        cap->size[cap->count] =
          can_test_message_read_all(rsp.message.content, cap->payload[cap->count], sizeof(cap->payload[cap->count]));
        cap->count++;
        cy_message_refcount_dec(rsp.message.content);
    }
}

static void on_request_server(cy_future_t* const future)
{
    request_server_t* const server = (request_server_t*)cy_future_context(future).ptr[0];
    TEST_ASSERT_NOT_NULL(server);
    if (!cy_future_done(future)) {
        return;
    }
    {
        cy_arrival_t arrival = cy_arrival_move(future);
        if (arrival.message.content == NULL) {
            return;
        }
        server->calls++;
        TEST_ASSERT_EQUAL_INT(CY_OK,
                              cy_respond(&arrival.breadcrumb,
                                         cy_now(arrival.breadcrumb.cy) + (20 * spin_slice_us),
                                         (cy_bytes_t){ server->response_a_size, server->response_a, NULL }));
        server->reliable_future =
          cy_respond_reliable(&arrival.breadcrumb,
                              cy_now(arrival.breadcrumb.cy) + (20 * spin_slice_us),
                              (cy_bytes_t){ server->response_b_size, server->response_b, NULL });
        TEST_ASSERT_NOT_NULL(server->reliable_future);
        cy_message_refcount_dec(arrival.message.content);
    }
}

static bool two_responses_received(void* const context)
{
    const response_capture_t* const cap = (const response_capture_t*)context;
    return cap->count >= 2U;
}

static void test_api_can_reliable_publish_success(void)
{
    const uint8_t payload[] = { 1U, 2U, 3U, 4U, 5U, 6U };

    can_test_bus_t  bus;
    can_test_node_t a;
    can_test_node_t b;
    can_test_bus_init(&bus);
    can_test_node_prepare(&a, &bus, 1U, false, false);
    can_test_node_prepare(&b, &bus, 1U, false, false);
    can_test_node_make_platform(&a, 256U, 0U);
    can_test_node_make_platform(&b, 256U, 0U);
    can_test_node_make_cy(&a, "reliable_pub_a");
    can_test_node_make_cy(&b, "reliable_pub_b");

    cy_publisher_t* const pub = cy_advertise(a.cy, cy_str("200#200"));
    cy_future_t* const    sub = cy_subscribe(b.cy, cy_str("200#200"), 64U);
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);

    cy_future_t* const fut =
      cy_publish_reliable(pub, cy_now(a.cy) + (30 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL });
    TEST_ASSERT_NOT_NULL(fut);
    TEST_ASSERT_TRUE(can_test_spin_pair_until_future_done(&a, &b, fut, 80U, spin_slice_us));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(fut));
    TEST_ASSERT_TRUE(cy_future_done(sub));

    {
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    cy_future_destroy(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);
    can_test_node_destroy(&a);
    can_test_node_destroy(&b);
}

static void test_api_can_reliable_publish_times_out_when_ack_is_lost(void)
{
    const uint8_t payload[] = { 9U, 8U, 7U, 6U };

    can_test_bus_t  bus;
    can_test_node_t a;
    can_test_node_t b;
    can_test_bus_init(&bus);
    can_test_node_prepare(&a, &bus, 1U, false, false);
    can_test_node_prepare(&b, &bus, 1U, false, false);
    can_test_node_make_platform(&a, 256U, 0U);
    can_test_node_make_platform(&b, 256U, 0U);
    can_test_node_make_cy(&a, "reliable_timeout_a");
    can_test_node_make_cy(&b, "reliable_timeout_b");

    cy_publisher_t* const pub = cy_advertise(a.cy, cy_str("201#201"));
    cy_future_t* const    sub = cy_subscribe(b.cy, cy_str("201#201"), 64U);
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);
    b.drop_tx[0] = true;

    cy_future_t* const fut =
      cy_publish_reliable(pub, cy_now(a.cy) + (20 * spin_slice_us), (cy_bytes_t){ sizeof(payload), payload, NULL });
    TEST_ASSERT_NOT_NULL(fut);
    TEST_ASSERT_TRUE(can_test_spin_pair_until_future_done(&a, &b, fut, 80U, spin_slice_us));
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(fut));
    TEST_ASSERT_TRUE(cy_future_done(sub));

    {
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, payload, sizeof(payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    cy_future_destroy(sub);
    can_test_spin_pair(&a, &b, 4U, spin_slice_us);
    can_test_node_destroy(&a);
    can_test_node_destroy(&b);
}

static void test_api_can_request_response_streaming_and_reliable_response(void)
{
    const uint8_t request_payload[] = { 0xAAU, 0xBBU, 0xCCU };

    can_test_bus_t     bus;
    can_test_node_t    client;
    can_test_node_t    server;
    response_capture_t capture;
    request_server_t   server_state;
    can_test_bus_init(&bus);
    can_test_node_prepare(&client, &bus, 1U, false, false);
    can_test_node_prepare(&server, &bus, 1U, false, false);
    can_test_node_make_platform(&client, 256U, 0U);
    can_test_node_make_platform(&server, 256U, 0U);
    can_test_node_make_cy(&client, "rpc_client");
    can_test_node_make_cy(&server, "rpc_server");
    (void)memset(&capture, 0, sizeof(capture));
    (void)memset(&server_state, 0, sizeof(server_state));
    server_state.response_a[0]   = 0x10U;
    server_state.response_a[1]   = 0x11U;
    server_state.response_a[2]   = 0x12U;
    server_state.response_a_size = 3U;
    server_state.response_b[0]   = 0x20U;
    server_state.response_b[1]   = 0x21U;
    server_state.response_b_size = 2U;

    cy_publisher_t* const pub = cy_advertise_client(client.cy, cy_str("202#202"), 64U);
    cy_future_t* const    sub = cy_subscribe(server.cy, cy_str("202#202"), 64U);
    TEST_ASSERT_NOT_NULL(pub);
    TEST_ASSERT_NOT_NULL(sub);
    {
        cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
        ctx.ptr[0]            = &server_state;
        cy_future_context_set(sub, ctx);
        cy_future_callback_set(sub, on_request_server);
    }
    can_test_spin_pair(&client, &server, 4U, spin_slice_us);

    cy_future_t* const req = cy_request(pub,
                                        cy_now(client.cy) + (30 * spin_slice_us),
                                        10 * spin_slice_us,
                                        (cy_bytes_t){ sizeof(request_payload), request_payload, NULL });
    TEST_ASSERT_NOT_NULL(req);
    {
        cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
        ctx.ptr[0]            = &capture;
        cy_future_context_set(req, ctx);
        cy_future_callback_set(req, on_response_capture);
    }

    TEST_ASSERT_TRUE(
      can_test_spin_pair_until_condition(&client, &server, two_responses_received, &capture, 120U, spin_slice_us));
    TEST_ASSERT_EQUAL_size_t(1U, server_state.calls);
    TEST_ASSERT_NOT_NULL(server_state.reliable_future);
    TEST_ASSERT_TRUE(
      can_test_spin_pair_until_future_done(&client, &server, server_state.reliable_future, 120U, spin_slice_us));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(server_state.reliable_future));
    TEST_ASSERT_EQUAL_size_t(2U, capture.count);
    TEST_ASSERT_EQUAL_UINT64(0U, capture.seqno[0]);
    TEST_ASSERT_EQUAL_UINT64(1U, capture.seqno[1]);
    TEST_ASSERT_EQUAL_size_t(server_state.response_a_size, capture.size[0]);
    TEST_ASSERT_EQUAL_size_t(server_state.response_b_size, capture.size[1]);
    TEST_ASSERT_EQUAL_UINT8_ARRAY(server_state.response_a, capture.payload[0], server_state.response_a_size);
    TEST_ASSERT_EQUAL_UINT8_ARRAY(server_state.response_b, capture.payload[1], server_state.response_b_size);

    cy_future_destroy(server_state.reliable_future);
    cy_future_destroy(req);
    cy_unadvertise(pub);
    cy_future_destroy(sub);
    can_test_spin_pair(&client, &server, 4U, spin_slice_us);
    can_test_node_destroy(&client);
    can_test_node_destroy(&server);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_reliable_publish_success);
    RUN_TEST(test_api_can_reliable_publish_times_out_when_ack_is_lost);
    RUN_TEST(test_api_can_request_response_streaming_and_reliable_response);
    return UNITY_END();
}
