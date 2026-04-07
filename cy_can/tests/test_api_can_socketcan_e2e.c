#include "test_support.h"
#include <cy_can_socketcan.h>
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

typedef struct
{
    size_t calls;
} socketcan_server_t;

static char* iface_name_buffer(void)
{
    static char value[16] = { 0 };
    return value;
}

static void sleep_2ms(void)
{
    const struct timespec ts = { .tv_sec = 0, .tv_nsec = 2 * 1000 * 1000 };
    (void)nanosleep(&ts, NULL);
}

static int run_cmd(const char* const command)
{
    TEST_ASSERT_NOT_NULL(command);
    return system(command); // NOLINT(cert-env33-c)
}

static int skip_with_reason(const char* const reason)
{
    (void)fprintf(stderr, "SKIP: %s\n", reason);
    return CAN_TEST_SKIP_CODE;
}

static int provision_vcan_interface(char* const out_name, const size_t out_size)
{
    char                command[256];
    const unsigned long tag = (unsigned long)getpid() % 100000UL;
    TEST_ASSERT_NOT_NULL(out_name);
    TEST_ASSERT_TRUE(out_size >= sizeof(iface_name_buffer()[0]) * 16U);
    (void)snprintf(out_name, out_size, "vcan%05lu", tag);

    if (run_cmd("command -v ip >/dev/null 2>&1") != 0) {
        return skip_with_reason("ip tool is unavailable");
    }
    if (run_cmd("sudo -n true >/dev/null 2>&1") != 0) {
        return skip_with_reason("passwordless sudo is unavailable");
    }
    if (run_cmd("sudo -n modprobe vcan >/dev/null 2>&1") != 0) {
        return skip_with_reason("vcan kernel module could not be loaded");
    }

    (void)snprintf(command, sizeof(command), "sudo -n ip link add dev %s type vcan >/dev/null 2>&1", out_name);
    if (run_cmd(command) != 0) {
        return skip_with_reason("failed to create vcan interface");
    }

    (void)snprintf(command, sizeof(command), "sudo -n ip link set dev %s up >/dev/null 2>&1", out_name);
    if (run_cmd(command) != 0) {
        (void)snprintf(command, sizeof(command), "sudo -n ip link del dev %s >/dev/null 2>&1", out_name);
        (void)run_cmd(command);
        return skip_with_reason("failed to bring vcan interface up");
    }
    return 0;
}

static void destroy_vcan_interface(const char* const iface_name)
{
    char command[256];
    if ((iface_name == NULL) || (iface_name[0] == '\0')) {
        return;
    }
    (void)snprintf(command, sizeof(command), "sudo -n ip link del dev %s >/dev/null 2>&1", iface_name);
    (void)run_cmd(command);
}

static void on_socketcan_request(cy_future_t* const future)
{
    socketcan_server_t* const state = (socketcan_server_t*)cy_future_context(future).ptr[0];
    TEST_ASSERT_NOT_NULL(state);
    if (!cy_future_done(future)) {
        return;
    }
    {
        const uint8_t response[] = { 0x91U, 0x92U, 0x93U };
        cy_arrival_t  arrival    = cy_arrival_move(future);
        if (arrival.message.content == NULL) {
            return;
        }
        state->calls++;
        TEST_ASSERT_EQUAL_INT(CY_OK,
                              cy_respond(&arrival.breadcrumb,
                                         cy_now(arrival.breadcrumb.cy) + 300000,
                                         (cy_bytes_t){ sizeof(response), response, NULL }));
        cy_message_refcount_dec(arrival.message.content);
    }
}

static void test_api_can_socketcan_e2e_smoke(void)
{
    const char*        ifaces[1]     = { iface_name_buffer() };
    const uint8_t      pub_payload[] = { 0x81U, 0x82U, 0x83U, 0x84U };
    const uint8_t      req_payload[] = { 0xA1U, 0xA2U };
    const uint8_t      rsp_payload[] = { 0x91U, 0x92U, 0x93U };
    socketcan_server_t server_state;
    cy_platform_t*     platform_a = NULL;
    cy_platform_t*     platform_b = NULL;
    cy_t*              cy_a       = NULL;
    cy_t*              cy_b       = NULL;
    cy_future_t*       sub        = NULL;
    cy_publisher_t*    pub        = NULL;
    cy_publisher_t*    client     = NULL;
    cy_future_t*       server_sub = NULL;
    cy_future_t*       req        = NULL;
    (void)memset(&server_state, 0, sizeof(server_state));

    platform_a = cy_can_socketcan_new(1U, ifaces, 256U);
    platform_b = cy_can_socketcan_new(1U, ifaces, 256U);
    TEST_ASSERT_NOT_NULL(platform_a);
    TEST_ASSERT_NOT_NULL(platform_b);

    cy_a = cy_new(platform_a, cy_str("socketcan_a"), (cy_str_t){ 0U, NULL });
    cy_b = cy_new(platform_b, cy_str("socketcan_b"), (cy_str_t){ 0U, NULL });
    TEST_ASSERT_NOT_NULL(cy_a);
    TEST_ASSERT_NOT_NULL(cy_b);

    sub = cy_subscribe(cy_b, cy_str("500#500"), 64U);
    pub = cy_advertise(cy_a, cy_str("500#500"));
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_NOT_NULL(pub);

    TEST_ASSERT_EQUAL_INT(
      CY_OK, cy_publish(pub, cy_now(cy_a) + 300000, (cy_bytes_t){ sizeof(pub_payload), pub_payload, NULL }));
    for (size_t i = 0U; (i < 200U) && !cy_future_done(sub); i++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(cy_a, cy_now(cy_a) + (cy_us_t)2000));
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(cy_b, cy_now(cy_b) + (cy_us_t)2000));
        sleep_2ms();
    }
    TEST_ASSERT_TRUE(cy_future_done(sub));
    {
        uint8_t            received[16];
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        TEST_ASSERT_EQUAL_size_t(sizeof(pub_payload), cy_message_size(arrival.message.content));
        TEST_ASSERT_EQUAL_size_t(sizeof(pub_payload),
                                 cy_message_read(arrival.message.content, 0U, sizeof(received), received));
        TEST_ASSERT_EQUAL_UINT8_ARRAY(pub_payload, received, sizeof(pub_payload));
        cy_message_refcount_dec(arrival.message.content);
    }

    client     = cy_advertise_client(cy_a, cy_str("501#501"), 64U);
    server_sub = cy_subscribe(cy_b, cy_str("501#501"), 64U);
    TEST_ASSERT_NOT_NULL(client);
    TEST_ASSERT_NOT_NULL(server_sub);
    {
        cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
        ctx.ptr[0]            = &server_state;
        cy_future_context_set(server_sub, ctx);
        cy_future_callback_set(server_sub, on_socketcan_request);
    }
    for (size_t i = 0U; i < 8U; i++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(cy_a, cy_now(cy_a) + (cy_us_t)2000));
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(cy_b, cy_now(cy_b) + (cy_us_t)2000));
        sleep_2ms();
    }

    req = cy_request(client, cy_now(cy_a) + 300000, 100000, (cy_bytes_t){ sizeof(req_payload), req_payload, NULL });
    TEST_ASSERT_NOT_NULL(req);
    for (size_t i = 0U; (i < 200U) && (cy_response_count(req) == 0U); i++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(cy_a, cy_now(cy_a) + (cy_us_t)2000));
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(cy_b, cy_now(cy_b) + (cy_us_t)2000));
        sleep_2ms();
    }
    TEST_ASSERT_EQUAL_size_t(1U, server_state.calls);
    TEST_ASSERT_TRUE(cy_response_count(req) > 0U);
    {
        uint8_t             received[16] = { 0 };
        const cy_response_t response     = cy_response_move(req);
        TEST_ASSERT_NOT_NULL(response.message.content);
        TEST_ASSERT_TRUE(cy_message_size(response.message.content) >= sizeof(rsp_payload));
        TEST_ASSERT_EQUAL_size_t(sizeof(rsp_payload),
                                 cy_message_read(response.message.content, 0U, sizeof(rsp_payload), received));
        TEST_ASSERT_EQUAL_UINT8_ARRAY(rsp_payload, received, sizeof(rsp_payload));
        cy_message_refcount_dec(response.message.content);
    }

    cy_future_destroy(req);
    cy_unadvertise(client);
    cy_future_destroy(server_sub);
    cy_unadvertise(pub);
    cy_future_destroy(sub);
    for (size_t i = 0U; i < 8U; i++) {
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(cy_a, cy_now(cy_a) + (cy_us_t)2000));
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(cy_b, cy_now(cy_b) + (cy_us_t)2000));
        sleep_2ms();
    }
    cy_destroy(cy_a);
    cy_destroy(cy_b);
    cy_can_socketcan_destroy(platform_a);
    cy_can_socketcan_destroy(platform_b);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    int result = 0;
    result     = provision_vcan_interface(iface_name_buffer(), sizeof(iface_name_buffer()[0]) * 16U);
    if (result != 0) {
        return result;
    }

    UNITY_BEGIN();
    RUN_TEST(test_api_can_socketcan_e2e_smoke);
    result = UNITY_END();

    destroy_vcan_interface(iface_name_buffer());
    return result;
}
