#ifndef _DEFAULT_SOURCE // NOLINT(*-reserved-identifier,*-dcl37-c,*-dcl51-cpp)
#define _DEFAULT_SOURCE // NOLINT(*-reserved-identifier,*-dcl37-c,*-dcl51-cpp)
#endif

#include "test_support.h"

#include <unity.h>
#include <udpard.h>

#include <arpa/inet.h>
#include <netinet/in.h>
#include <signal.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

static const cy_us_t spin_slice_us = (cy_us_t)5000;

typedef struct
{
    cy_future_t* future;
    uint64_t     minimum_count;
} arrival_count_context_t;

static volatile sig_atomic_t g_signal_seen = 0; // NOLINT(cppcoreguidelines-avoid-non-const-global-variables)

static bool has_arrival_count(void* const context)
{
    const arrival_count_context_t* const ctx = (const arrival_count_context_t*)context;
    return (ctx != NULL) && (cy_arrival_count(ctx->future) >= ctx->minimum_count);
}

static void on_signal(const int signum)
{
    (void)signum;
    g_signal_seen = 1;
}

static void wait_for_new_wall_second(void)
{
    const time_t    started = time(NULL);
    struct timespec delay   = { .tv_sec = 0, .tv_nsec = 10000000L };
    while (time(NULL) == started) {
        (void)nanosleep(&delay, NULL);
    }
}

static void send_subject_datagram(const uint32_t subject_id, const void* const payload, const size_t size)
{
    const udpard_udpip_ep_t ep = udpard_make_subject_endpoint(subject_id);
    const int               fd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
    TEST_ASSERT_TRUE(fd >= 0);

    const struct in_addr iface = { .s_addr = htonl(0x7F000001U) };
    const unsigned char  loop  = 1U;
    TEST_ASSERT_EQUAL_INT(0, setsockopt(fd, IPPROTO_IP, IP_MULTICAST_IF, &iface, sizeof(iface)));
    TEST_ASSERT_EQUAL_INT(0, setsockopt(fd, IPPROTO_IP, IP_MULTICAST_LOOP, &loop, sizeof(loop)));

    const struct sockaddr_in dst = {
        .sin_family = AF_INET,
        .sin_addr   = { .s_addr = htonl(ep.ip) },
        .sin_port   = htons(ep.port),
    };
    const ssize_t sent = sendto(fd, payload, size, 0, (const struct sockaddr*)&dst, sizeof(dst));
    TEST_ASSERT_TRUE(sent >= 0);
    TEST_ASSERT_EQUAL_size_t(size, (size_t)sent);
    TEST_ASSERT_EQUAL_INT(0, close(fd));
}

static void assert_mem_stats_equal(const cy_udp_posix_stats_t expected, const cy_udp_posix_stats_t actual)
{
    TEST_ASSERT_EQUAL_size_t(expected.mem.allocated_fragments, actual.mem.allocated_fragments);
    TEST_ASSERT_EQUAL_size_t(expected.mem.allocated_bytes, actual.mem.allocated_bytes);
    TEST_ASSERT_EQUAL_UINT64(expected.mem.oom_count, actual.mem.oom_count);
}

static bool run_same_second_restart_attempt(bool* const out_arrived)
{
    static const uint64_t sender_uid   = UINT64_C(0xD000000000000001);
    static const uint64_t receiver_uid = UINT64_C(0xD000000000000002);
    static const uint8_t  payload_a[]  = { 0x11U };
    static const uint8_t  payload_b[]  = { 0x22U };

    TEST_ASSERT_NOT_NULL(out_arrived);
    *out_arrived = false;

    udp_test_node_t sender_a;
    udp_test_node_t sender_b;
    udp_test_node_t receiver;
    udp_test_node_init_manual(&receiver, receiver_uid, "udp_restart_receiver", 256U);
    cy_future_t* const sub = cy_subscribe(receiver.cy, cy_str("udp/restart#401"), 64U);
    TEST_ASSERT_NOT_NULL(sub);

    const time_t ctor_second = time(NULL);
    udp_test_node_init_manual(&sender_a, sender_uid, "udp_restart_sender_a", 256U);
    {
        const struct timespec delay = { .tv_sec = 0, .tv_nsec = 3000000L };
        (void)nanosleep(&delay, NULL);
    }
    udp_test_node_init_manual(&sender_b, sender_uid, "udp_restart_sender_b", 256U);
    if (time(NULL) != ctor_second) {
        cy_future_destroy(sub);
        udp_test_spin_pair(&sender_a, &receiver, 2U, spin_slice_us);
        udp_test_spin_pair(&sender_b, &receiver, 2U, spin_slice_us);
        udp_test_node_deinit(&sender_a);
        udp_test_node_deinit(&sender_b);
        udp_test_node_deinit(&receiver);
        return false;
    }

    cy_publisher_t* const pub_a = cy_advertise(sender_a.cy, cy_str("udp/restart#401"));
    cy_publisher_t* const pub_b = cy_advertise(sender_b.cy, cy_str("udp/restart#401"));
    TEST_ASSERT_NOT_NULL(pub_a);
    TEST_ASSERT_NOT_NULL(pub_b);
    udp_test_spin_pair(&sender_a, &receiver, 3U, spin_slice_us);
    udp_test_spin_pair(&sender_b, &receiver, 3U, spin_slice_us);
    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_publish(pub_a,
                                     cy_now(sender_a.cy) + (40 * spin_slice_us),
                                     (cy_bytes_t){ sizeof(payload_a), payload_a, NULL }));
    {
        arrival_count_context_t ctx = { .future = sub, .minimum_count = 1U };
        TEST_ASSERT_TRUE(
          udp_test_spin_pair_until_condition(&sender_a, &receiver, has_arrival_count, &ctx, 80U, spin_slice_us));
    }
    {
        const cy_arrival_t arrival = cy_arrival_move(sub);
        TEST_ASSERT_NOT_NULL(arrival.message.content);
        udp_test_assert_message_equals(arrival.message.content, payload_a, sizeof(payload_a));
        cy_message_refcount_dec(arrival.message.content);
    }
    cy_unadvertise(pub_a);
    udp_test_node_deinit(&sender_a);

    TEST_ASSERT_EQUAL_INT(CY_OK,
                          cy_publish(pub_b,
                                     cy_now(sender_b.cy) + (40 * spin_slice_us),
                                     (cy_bytes_t){ sizeof(payload_b), payload_b, NULL }));
    {
        arrival_count_context_t ctx = { .future = sub, .minimum_count = 2U };
        const bool              ok =
          udp_test_spin_pair_until_condition(&sender_b, &receiver, has_arrival_count, &ctx, 80U, spin_slice_us);
        if (ok) {
            const cy_arrival_t arrival = cy_arrival_move(sub);
            TEST_ASSERT_NOT_NULL(arrival.message.content);
            udp_test_assert_message_equals(arrival.message.content, payload_b, sizeof(payload_b));
            cy_message_refcount_dec(arrival.message.content);
        }
        cy_unadvertise(pub_b);
        cy_future_destroy(sub);
        udp_test_spin_pair(&sender_b, &receiver, 4U, spin_slice_us);
        udp_test_node_deinit(&sender_b);
        udp_test_node_deinit(&receiver);
        *out_arrived = ok;
        return true;
    }
}

static void set_signal_timer(const suseconds_t first_us, const suseconds_t interval_us)
{
    const struct itimerval timer = {
        .it_interval = { .tv_sec = 0, .tv_usec = interval_us },
        .it_value    = { .tv_sec = 0, .tv_usec = first_us },
    };
    TEST_ASSERT_EQUAL_INT(0, setitimer(ITIMER_REAL, &timer, NULL));
}

static void test_api_udp_posix_rx_drops_malformed_datagrams_without_leak(void)
{
    static const uint32_t subject_id  = 402U;
    static const uint8_t  one[]       = { 0x01U };
    static const uint8_t  short_msg[] = { 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U, 0x08U };
    udp_test_node_t       node;

    udp_test_node_init_manual(&node, UINT64_C(0xE000000000000001), "udp_malformed", 256U);
    cy_future_t* const sub = cy_subscribe(node.cy, cy_str("udp/malformed#402"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    udp_test_spin(&node, spin_slice_us);
    for (size_t i = 0U; i < 12U; i++) {
        udp_test_spin(&node, spin_slice_us);
    }

    const cy_udp_posix_stats_t baseline = cy_udp_posix_stats(node.platform);
    send_subject_datagram(subject_id, one, 0U);
    send_subject_datagram(subject_id, one, sizeof(one));
    send_subject_datagram(subject_id, short_msg, sizeof(short_msg));
    for (size_t i = 0U; i < 12U; i++) {
        udp_test_spin(&node, spin_slice_us);
    }

    TEST_ASSERT_EQUAL_UINT64(0U, cy_arrival_count(sub));
    assert_mem_stats_equal(baseline, cy_udp_posix_stats(node.platform));

    cy_future_destroy(sub);
    udp_test_spin(&node, spin_slice_us);
    udp_test_node_deinit(&node);
}

static void test_api_udp_posix_manual_restart_uses_fresh_transfer_id_seed(void)
{
    bool exercised = false;
    for (size_t attempt = 0U; (attempt < 8U) && !exercised; attempt++) {
        wait_for_new_wall_second();
        bool arrived = false;
        if (run_same_second_restart_attempt(&arrived)) {
            exercised = true;
            TEST_ASSERT_TRUE(arrived);
        }
    }
    TEST_ASSERT_TRUE(exercised);
}

static void test_api_udp_posix_spin_retries_after_signal_eintr(void)
{
    udp_test_node_t node;
    udp_test_node_init_manual(&node, UINT64_C(0xE000000000000002), "udp_eintr", 256U);

    struct sigaction action;
    struct sigaction old_action;
    (void)memset(&action, 0, sizeof(action));
    TEST_ASSERT_EQUAL_INT(0, sigemptyset(&action.sa_mask));
    action.sa_handler = on_signal;
    TEST_ASSERT_EQUAL_INT(0, sigaction(SIGALRM, &action, &old_action));
    g_signal_seen = 0;

    set_signal_timer(10000, 10000);
    const cy_err_t err = cy_spin_until(node.cy, cy_now(node.cy) + 120000);
    set_signal_timer(0, 0);
    TEST_ASSERT_EQUAL_INT(0, sigaction(SIGALRM, &old_action, NULL));
    TEST_ASSERT_TRUE(g_signal_seen != 0);
    TEST_ASSERT_EQUAL_INT(CY_OK, err);

    udp_test_node_deinit(&node);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_udp_posix_rx_drops_malformed_datagrams_without_leak);
    RUN_TEST(test_api_udp_posix_manual_restart_uses_fresh_transfer_id_seed);
    RUN_TEST(test_api_udp_posix_spin_retries_after_signal_eintr);
    return UNITY_END();
}
