#include "test_support.h"

#include <unity.h>

#include <stdlib.h>
#include <string.h>

static void test_api_udp_posix_basic_parse_iface_address(void)
{
    TEST_ASSERT_EQUAL_HEX32(0x7F000001U, cy_udp_parse_iface_address("127.0.0.1"));
    TEST_ASSERT_EQUAL_HEX32(0U, cy_udp_parse_iface_address("127.0.0"));
    TEST_ASSERT_EQUAL_HEX32(0U, cy_udp_parse_iface_address("not_an_ip"));
    TEST_ASSERT_EQUAL_HEX32(0U, cy_udp_parse_iface_address(NULL));
}

static void test_api_udp_posix_basic_manual_constructor_and_home(void)
{
    static const uint32_t no_ifaces[CY_UDP_POSIX_IFACE_COUNT_MAX]      = { 0U, 0U, 0U };
    static const uint32_t loopback_iface[CY_UDP_POSIX_IFACE_COUNT_MAX] = { 0x7F000001U, 0U, 0U };
    cy_platform_t*        platform                                     = NULL;
    cy_str_t              home;
    cy_udp_posix_stats_t  stats;

    TEST_ASSERT_NULL(cy_udp_posix_new_manual(UINT64_C(0x0123456789ABCDEF), no_ifaces, 16U));

    platform = cy_udp_posix_new_manual(UINT64_C(0x0123456789ABCDEF), loopback_iface, 64U);
    TEST_ASSERT_NOT_NULL(platform);

    home = cy_udp_posix_home(platform, NULL);
    TEST_ASSERT_EQUAL_size_t(16U, home.len);
    TEST_ASSERT_EQUAL_STRING_LEN("0123456789abcdef", home.str, 16);

    home = cy_udp_posix_home(platform, "udp");
    TEST_ASSERT_EQUAL_size_t(strlen("udp/0123456789abcdef"), home.len);
    TEST_ASSERT_EQUAL_STRING_LEN("udp/0123456789abcdef", home.str, home.len);

    stats = cy_udp_posix_stats(platform);
    TEST_ASSERT_EQUAL_size_t(0U, stats.subject_writer_count);
    TEST_ASSERT_EQUAL_size_t(0U, stats.subject_reader_count);
    TEST_ASSERT_EQUAL_size_t(0U, stats.mem.allocated_fragments);
    TEST_ASSERT_EQUAL_size_t(0U, stats.mem.allocated_bytes);
    TEST_ASSERT_EQUAL_UINT64(0U, stats.mem.oom_count);
    TEST_ASSERT_EQUAL_UINT64(0U, stats.message_loss_count);
    for (size_t i = 0U; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        TEST_ASSERT_EQUAL_UINT64(0U, stats.sock_tx.error_count[i]);
        TEST_ASSERT_EQUAL_UINT64(0U, stats.sock_rx.error_count[i]);
    }
    TEST_ASSERT_EQUAL_INT64(0, stats.sock_tx.last_error_at);
    TEST_ASSERT_EQUAL_INT64(0, stats.sock_rx.last_error_at);

    cy_udp_posix_destroy(platform);
}

static void test_api_udp_posix_basic_namespace_and_time(void)
{
    const char* const old_env = getenv("CYPHAL_NAMESPACE");
    char* const       backup  = (old_env != NULL) ? strdup(old_env) : NULL;
    const cy_us_t     t0      = cy_udp_posix_now();
    const cy_us_t     t1      = cy_udp_posix_now();

    TEST_ASSERT_TRUE(t1 >= t0);

    TEST_ASSERT_EQUAL_INT(0, setenv("CYPHAL_NAMESPACE", "ns/test", 1));
    {
        const cy_str_t ns = cy_udp_posix_namespace();
        TEST_ASSERT_EQUAL_size_t(strlen("ns/test"), ns.len);
        TEST_ASSERT_EQUAL_STRING_LEN("ns/test", ns.str, ns.len);
    }

    TEST_ASSERT_EQUAL_INT(0, unsetenv("CYPHAL_NAMESPACE"));
    {
        const cy_str_t ns = cy_udp_posix_namespace();
        TEST_ASSERT_EQUAL_size_t(0U, ns.len);
    }

    if (backup != NULL) {
        TEST_ASSERT_EQUAL_INT(0, setenv("CYPHAL_NAMESPACE", backup, 1));
        free(backup);
    }
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_api_udp_posix_basic_parse_iface_address);
    RUN_TEST(test_api_udp_posix_basic_manual_constructor_and_home);
    RUN_TEST(test_api_udp_posix_basic_namespace_and_time);
    return UNITY_END();
}
