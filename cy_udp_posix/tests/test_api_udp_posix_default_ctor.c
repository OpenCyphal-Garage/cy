#include "test_support.h"

#include <unity.h>

#include <stdio.h>

static void test_api_udp_posix_default_ctor_hostname_hash_and_flags(void)
{
    cy_platform_t* const platform_a = cy_udp_posix_new();
    cy_platform_t* const platform_b = cy_udp_posix_new();
    const uint32_t       expected   = udp_test_expected_eui64_prefix();

    TEST_ASSERT_NOT_NULL(platform_a);
    TEST_ASSERT_NOT_NULL(platform_b);

    {
        const uint64_t uid_a = udp_test_parse_uid_from_home(cy_udp_posix_home(platform_a, NULL));
        const uint64_t uid_b = udp_test_parse_uid_from_home(cy_udp_posix_home(platform_b, NULL));

        TEST_ASSERT_EQUAL_HEX32(expected, (uint32_t)(uid_a >> 44U));
        TEST_ASSERT_EQUAL_HEX32(expected, (uint32_t)(uid_b >> 44U));
        TEST_ASSERT_TRUE((uid_a & (1ULL << 57U)) != 0U);
        TEST_ASSERT_TRUE((uid_b & (1ULL << 57U)) != 0U);
        TEST_ASSERT_TRUE((uid_a & (1ULL << 56U)) == 0U);
        TEST_ASSERT_TRUE((uid_b & (1ULL << 56U)) == 0U);
    }

    cy_udp_posix_destroy(platform_a);
    cy_udp_posix_destroy(platform_b);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    cy_platform_t* const probe_a = cy_udp_posix_new();
    cy_platform_t* const probe_b = cy_udp_posix_new();
    if ((probe_a == NULL) || (probe_b == NULL)) {
        cy_udp_posix_destroy(probe_a);
        cy_udp_posix_destroy(probe_b);
        (void)fprintf(stderr, "cy_udp_posix_new() unavailable on this host, skipping default-constructor smoke test\n");
        return UDP_TEST_SKIP_CODE;
    }
    cy_udp_posix_destroy(probe_a);
    cy_udp_posix_destroy(probe_b);

    UNITY_BEGIN();
    RUN_TEST(test_api_udp_posix_default_ctor_hostname_hash_and_flags);
    return UNITY_END();
}
