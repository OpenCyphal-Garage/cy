#pragma once

#include <cy_udp_posix.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define UDP_TEST_SKIP_CODE 77

typedef struct
{
    cy_platform_t* platform;
    cy_t*          cy;
    uint64_t       uid;
} udp_test_node_t;

void udp_test_node_init_manual(udp_test_node_t* self, uint64_t uid, const char* home_prefix, size_t tx_queue_capacity);
void udp_test_node_deinit(udp_test_node_t* self);

void udp_test_spin(udp_test_node_t* node, cy_us_t slice);
void udp_test_spin_pair(udp_test_node_t* a, udp_test_node_t* b, size_t rounds, cy_us_t slice);
bool udp_test_spin_pair_until_condition(udp_test_node_t* a,
                                        udp_test_node_t* b,
                                        bool (*condition)(void*),
                                        void*   context,
                                        size_t  rounds,
                                        cy_us_t slice);

size_t   udp_test_message_read_all(const cy_message_t* message, void* out, size_t capacity);
void     udp_test_assert_message_equals(const cy_message_t* message, const void* expected, size_t size);
void     udp_test_fill_payload(uint8_t* out, size_t size, uint8_t seed);
uint64_t udp_test_parse_uid_from_home(const cy_str_t home);
uint32_t udp_test_hostname_hash20(void);
uint32_t udp_test_expected_eui64_prefix(void);

#ifdef __cplusplus
}
#endif
