#include "test_support.h"

#include <unity.h>

#define RAPIDHASH_COMPACT
#include <rapidhash.h>

#include <stdlib.h>
#include <string.h>
#include <unistd.h>

void udp_test_node_init_manual(udp_test_node_t* const self,
                               const uint64_t         uid,
                               const char* const      home_prefix,
                               const size_t           tx_queue_capacity)
{
    static const uint32_t iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX] = { 0x7F000001U, 0U, 0U };
    TEST_ASSERT_NOT_NULL(self);
    (void)memset(self, 0, sizeof(*self));
    self->uid      = uid;
    self->platform = cy_udp_posix_new_manual(uid, iface_address, tx_queue_capacity);
    TEST_ASSERT_NOT_NULL(self->platform);
    self->cy = cy_new(self->platform, cy_udp_posix_home(self->platform, home_prefix), cy_str(""));
    TEST_ASSERT_NOT_NULL(self->cy);
}

void udp_test_node_deinit(udp_test_node_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    if (self->cy != NULL) {
        cy_destroy(self->cy);
        self->cy = NULL;
    }
    if (self->platform != NULL) {
        cy_udp_posix_destroy(self->platform);
        self->platform = NULL;
    }
}

void udp_test_spin(udp_test_node_t* const node, const cy_us_t slice)
{
    TEST_ASSERT_NOT_NULL(node);
    TEST_ASSERT_NOT_NULL(node->cy);
    TEST_ASSERT_TRUE(slice >= 0);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(node->cy, cy_now(node->cy) + slice));
}

void udp_test_spin_pair(udp_test_node_t* const a, udp_test_node_t* const b, const size_t rounds, const cy_us_t slice)
{
    for (size_t i = 0U; i < rounds; i++) {
        if (a != NULL) {
            udp_test_spin(a, slice);
        }
        if (b != NULL) {
            udp_test_spin(b, slice);
        }
    }
}

bool udp_test_spin_pair_until_condition(udp_test_node_t* const a,
                                        udp_test_node_t* const b,
                                        bool (*const condition)(void*),
                                        void* const   context,
                                        const size_t  rounds,
                                        const cy_us_t slice)
{
    TEST_ASSERT_NOT_NULL(condition);
    for (size_t i = 0U; i < rounds; i++) {
        if (condition(context)) {
            return true;
        }
        udp_test_spin_pair(a, b, 1U, slice);
    }
    return condition(context);
}

size_t udp_test_message_read_all(const cy_message_t* const message, void* const out, const size_t capacity)
{
    TEST_ASSERT_NOT_NULL(message);
    TEST_ASSERT_NOT_NULL(out);
    const size_t size = cy_message_size(message);
    TEST_ASSERT_TRUE(size <= capacity);
    TEST_ASSERT_EQUAL_size_t(size, cy_message_read(message, 0U, size, out));
    return size;
}

void udp_test_assert_message_equals(const cy_message_t* const message, const void* const expected, const size_t size)
{
    uint8_t buffer[4096];
    TEST_ASSERT_TRUE(size <= sizeof(buffer));
    TEST_ASSERT_EQUAL_size_t(size, udp_test_message_read_all(message, buffer, sizeof(buffer)));
    TEST_ASSERT_EQUAL_UINT8_ARRAY(expected, buffer, size);
}

void udp_test_fill_payload(uint8_t* const out, const size_t size, const uint8_t seed)
{
    TEST_ASSERT_NOT_NULL(out);
    for (size_t i = 0U; i < size; i++) {
        out[i] = (uint8_t)(seed + (uint8_t)i);
    }
}

uint64_t udp_test_parse_uid_from_home(const cy_str_t home)
{
    char   buffer[17] = { 0 };
    size_t start      = 0U;
    TEST_ASSERT_NOT_NULL(home.str);
    for (size_t i = 0U; i < home.len; i++) {
        if (home.str[i] == '/') {
            start = i + 1U;
        }
    }
    TEST_ASSERT_TRUE(home.len >= start);
    TEST_ASSERT_EQUAL_size_t(16U, home.len - start);
    (void)memcpy(buffer, &home.str[start], 16U);
    return (uint64_t)strtoull(buffer, NULL, 16);
}

uint32_t udp_test_hostname_hash20(void)
{
    char hostname[256] = { 0 };
    TEST_ASSERT_EQUAL_INT(0, gethostname(hostname, sizeof(hostname)));
    hostname[sizeof(hostname) - 1U] = 0;
    TEST_ASSERT_TRUE(hostname[0] != 0);
    return (uint32_t)(rapidhash(hostname, strlen(hostname)) & 0xFFFFFU);
}

uint32_t udp_test_expected_eui64_prefix(void)
{
    uint32_t out = udp_test_hostname_hash20();
    out &= ~(1U << 12U);
    out |= 1U << 13U;
    return out;
}
