#include "test_support.h"
#include <canard.h>
#include <cy_platform.h>
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

static const cy_us_t  spin_slice_us = (cy_us_t)10000;
static const uint16_t service_id    = 123U;

typedef struct
{
    size_t        count;
    size_t        multiframe_count;
    canard_prio_t priority;
    uint_least8_t source_node_id;
    uint_least8_t transfer_id;
    size_t        payload_size;
    uint8_t       payload[256];
} capture_t;

typedef struct
{
    const capture_t* capture;
    size_t           count;
} capture_goal_t;

static bool capture_goal_reached(void* const context)
{
    const capture_goal_t* const goal = (const capture_goal_t*)context;
    return goal->capture->count >= goal->count;
}

static void spin_until_capture(can_test_node_t* const a,
                               can_test_node_t* const b,
                               const capture_t* const capture,
                               const size_t           count)
{
    const capture_goal_t goal = { .capture = capture, .count = count };
    TEST_ASSERT_TRUE(can_test_spin_pair_until_condition(a, b, capture_goal_reached, (void*)&goal, 128U, spin_slice_us));
    TEST_ASSERT_EQUAL_size_t(count, capture->count);
}

static void on_transfer(canard_subscription_t* const self,
                        const canard_us_t            timestamp,
                        const canard_prio_t          priority,
                        const uint_least8_t          source_node_id,
                        const uint_least8_t          transfer_id,
                        const canard_payload_t       payload)
{
    capture_t* const capture = (capture_t*)self->user_context;
    (void)timestamp;
    TEST_ASSERT_NOT_NULL(capture);
    TEST_ASSERT_TRUE(payload.view.size <= sizeof(capture->payload));
    capture->count++;
    capture->priority       = priority;
    capture->source_node_id = source_node_id;
    capture->transfer_id    = transfer_id;
    capture->payload_size   = payload.view.size;
    if (payload.view.size > 0U) {
        (void)memcpy(capture->payload, payload.view.data, payload.view.size);
    }
    if (payload.origin.data != NULL) {
        const canard_mem_t mem = self->owner->mem.rx_payload;
        capture->multiframe_count++;
        mem.vtable->free(mem, payload.origin.size, payload.origin.data);
    }
}

static const canard_subscription_vtable_t sub_vtable = { .on_message = on_transfer };

static canard_bytes_chain_t make_payload(const void* const data, const size_t size)
{
    return (canard_bytes_chain_t){ .bytes = { .size = size, .data = data }, .next = NULL };
}

// CAN FD multi-frame transfers may be zero-padded up to the nearest valid frame length, per the Cyphal/CAN spec.
static void assert_payload(const capture_t* const capture,
                           const uint8_t* const   expected,
                           const size_t           size,
                           const bool             fd)
{
    TEST_ASSERT_TRUE(capture->payload_size >= size);
    TEST_ASSERT_TRUE((capture->payload_size == size) || (fd && (capture->multiframe_count > 0U)));
    TEST_ASSERT_TRUE((capture->payload_size - size) < 16U);
    TEST_ASSERT_EQUAL_INT(0, memcmp(expected, capture->payload, size));
    for (size_t i = size; i < capture->payload_size; i++) {
        TEST_ASSERT_EQUAL_UINT8(0U, capture->payload[i]);
    }
}

static void test_api_can_canard_rejects_foreign_platform(void)
{
    cy_platform_t foreign;
    (void)memset(&foreign, 0, sizeof(foreign));
    TEST_ASSERT_NULL(cy_can_canard(NULL));
    TEST_ASSERT_NULL(cy_can_canard(&foreign));
}

static void test_api_can_canard_exposes_the_live_shared_instance(void)
{
    can_test_bus_t        bus;
    can_test_node_t       node;
    canard_subscription_t intruder;
    can_test_bus_init(&bus);
    can_test_node_prepare(&node, &bus, 1U, false, false);
    can_test_node_make_platform(&node, 64U, 0U);

    canard_t* const canard = cy_can_canard(node.platform);
    TEST_ASSERT_NOT_NULL(canard);
    TEST_ASSERT_TRUE(canard == cy_can_canard(node.platform));
    TEST_ASSERT_TRUE(canard->user_context == (void*)node.platform);
    TEST_ASSERT_TRUE(canard->node_id <= CANARD_NODE_ID_MAX);
    TEST_ASSERT_FALSE(canard->tx.fd);

    canard_subscription_t* const unicast = canard_find_subscription(canard, canard_kind_request, 511U);
    TEST_ASSERT_NOT_NULL(unicast);
    TEST_ASSERT_TRUE(unicast == canard_subscribe_request(canard, &intruder, 511U, 64U, 0, &sub_vtable));

    can_test_node_make_cy(&node, "canard_live");
    TEST_ASSERT_TRUE(canard == cy_can_canard(node.platform));
    can_test_node_destroy(&node);
}

static void run_rpc_roundtrip(const bool fd_capable, const size_t request_size, const size_t response_size)
{
    static const uint8_t cy_payload[] = { 0xA1U, 0xB2U, 0xC3U, 0xD4U };
    uint8_t              request[200];
    uint8_t              response[200];

    can_test_bus_t        bus;
    can_test_node_t       client;
    can_test_node_t       server;
    capture_t             server_capture = { 0 };
    capture_t             client_capture = { 0 };
    canard_subscription_t server_sub;
    canard_subscription_t client_sub;
    TEST_ASSERT_TRUE((request_size <= sizeof(request)) && (response_size <= sizeof(response)));
    can_test_fill_payload(request, request_size, 0x10U);
    can_test_fill_payload(response, response_size, 0x80U);
    can_test_bus_init(&bus);
    can_test_node_prepare(&client, &bus, 1U, fd_capable, false);
    can_test_node_prepare(&server, &bus, 1U, fd_capable, false);
    can_test_node_make_platform(&client, 256U, 0U);
    can_test_node_make_platform(&server, 256U, 0U);
    can_test_node_make_cy(&client, "canard_client");
    can_test_node_make_cy(&server, "canard_server");

    canard_t* const client_canard = cy_can_canard(client.platform);
    canard_t* const server_canard = cy_can_canard(server.platform);
    TEST_ASSERT_NOT_NULL(client_canard);
    TEST_ASSERT_NOT_NULL(server_canard);
    TEST_ASSERT_TRUE(client_canard != server_canard);
    TEST_ASSERT_TRUE(client_canard->node_id != server_canard->node_id);

    TEST_ASSERT_TRUE(&server_sub == canard_subscribe_request(server_canard,
                                                             &server_sub,
                                                             service_id,
                                                             sizeof(server_capture.payload),
                                                             CANARD_DEFAULT_TRANSFER_ID_TIMEOUT_us,
                                                             &sub_vtable));
    server_sub.user_context = &server_capture;
    TEST_ASSERT_TRUE(
      &client_sub ==
      canard_subscribe_response(client_canard, &client_sub, service_id, sizeof(client_capture.payload), &sub_vtable));
    client_sub.user_context = &client_capture;

    // Run ordinary Cy traffic through the same instances to prove coexistence.
    cy_future_t* const    cy_sub = cy_subscribe(server.cy, cy_str("444#444"), 32U);
    cy_publisher_t* const cy_pub = cy_advertise(client.cy, cy_str("444#444"));
    TEST_ASSERT_NOT_NULL(cy_sub);
    TEST_ASSERT_NOT_NULL(cy_pub);
    can_test_spin_pair(&client, &server, 4U, spin_slice_us);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_publish(cy_pub,
                                     cy_now(client.cy) + (20 * spin_slice_us),
                                     (cy_bytes_t){ sizeof(cy_payload), cy_payload, NULL }));

    const uint_least8_t client_node_id = client_canard->node_id;
    const uint_least8_t server_node_id = server_canard->node_id;
    TEST_ASSERT_TRUE(canard_request(client_canard,
                                    cy_now(client.cy) + (40 * spin_slice_us),
                                    canard_prio_fast,
                                    service_id,
                                    server_node_id,
                                    17U,
                                    make_payload(request, request_size),
                                    NULL));
    spin_until_capture(&client, &server, &server_capture, 1U);
    TEST_ASSERT_EQUAL_size_t(0U, client_capture.count);
    assert_payload(&server_capture, request, request_size, fd_capable);
    TEST_ASSERT_EQUAL_UINT8(client_node_id, server_capture.source_node_id);
    TEST_ASSERT_EQUAL_UINT8(17U, server_capture.transfer_id);
    TEST_ASSERT_EQUAL_INT(canard_prio_fast, server_capture.priority);

    // The response is sent after the spin call has returned, as required by the reentrancy constraint.
    TEST_ASSERT_TRUE(canard_respond(server_canard,
                                    cy_now(server.cy) + (40 * spin_slice_us),
                                    server_capture.priority,
                                    service_id,
                                    server_capture.source_node_id,
                                    server_capture.transfer_id,
                                    make_payload(response, response_size),
                                    NULL));
    spin_until_capture(&client, &server, &client_capture, 1U);
    TEST_ASSERT_EQUAL_size_t(1U, server_capture.count);
    assert_payload(&client_capture, response, response_size, fd_capable);
    TEST_ASSERT_EQUAL_UINT8(server_node_id, client_capture.source_node_id);
    TEST_ASSERT_EQUAL_UINT8(17U, client_capture.transfer_id);
    TEST_ASSERT_EQUAL_INT(canard_prio_fast, client_capture.priority);

    const size_t mtu_payload = fd_capable ? (CANARD_MTU_CAN_FD - 1U) : (CANARD_MTU_CAN_CLASSIC - 1U);
    TEST_ASSERT_EQUAL_size_t((request_size > mtu_payload) ? 1U : 0U, server_capture.multiframe_count);
    TEST_ASSERT_EQUAL_size_t((response_size > mtu_payload) ? 1U : 0U, client_capture.multiframe_count);

    TEST_ASSERT_TRUE(can_test_spin_pair_until_future_done(&client, &server, cy_sub, 128U, spin_slice_us));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(cy_sub));
    {
        const cy_arrival_t arrival = cy_arrival_move(cy_sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        can_test_assert_message_equals(arrival.message.content, cy_payload, sizeof(cy_payload));
        cy_message_refcount_dec(arrival.message.content);
    }
    TEST_ASSERT_EQUAL_size_t(1U, server_capture.count);
    TEST_ASSERT_EQUAL_size_t(1U, client_capture.count);
    TEST_ASSERT_EQUAL_UINT64(0U, client_canard->err.oom + server_canard->err.oom);
    TEST_ASSERT_EQUAL_UINT64(0U, client_canard->err.rx_transfer + server_canard->err.rx_transfer);
    TEST_ASSERT_EQUAL_UINT8(client_node_id, client_canard->node_id);
    TEST_ASSERT_EQUAL_UINT8(server_node_id, server_canard->node_id);

    canard_unsubscribe(server_canard, &server_sub);
    canard_unsubscribe(client_canard, &client_sub);
    cy_unadvertise(cy_pub);
    cy_future_destroy(cy_sub);
    can_test_spin_pair(&client, &server, 1U, spin_slice_us);
    can_test_node_destroy(&client);
    can_test_node_destroy(&server);
}

static void test_api_can_canard_rpc_roundtrip_single_frame_classic(void) { run_rpc_roundtrip(false, 5U, 7U); }
static void test_api_can_canard_rpc_roundtrip_multiframe_classic(void) { run_rpc_roundtrip(false, 40U, 150U); }
static void test_api_can_canard_rpc_roundtrip_single_frame_fd(void) { run_rpc_roundtrip(true, 63U, 0U); }
static void test_api_can_canard_rpc_roundtrip_multiframe_fd(void) { run_rpc_roundtrip(true, 64U, 200U); }

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_can_canard_rejects_foreign_platform);
    RUN_TEST(test_api_can_canard_exposes_the_live_shared_instance);
    RUN_TEST(test_api_can_canard_rpc_roundtrip_single_frame_classic);
    RUN_TEST(test_api_can_canard_rpc_roundtrip_multiframe_classic);
    RUN_TEST(test_api_can_canard_rpc_roundtrip_single_frame_fd);
    RUN_TEST(test_api_can_canard_rpc_roundtrip_multiframe_fd);
    return UNITY_END();
}
