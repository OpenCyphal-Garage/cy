//                            ____                   ______            __          __
//                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
//                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
//                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
//                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
//                             /_/                     /____/_/
//
// A Cy platform layer for POSIX-like OSes using standard BSD sockets and libUDPard for Cyphal over UDP.
// It can be adapted to other socket-based APIs with minimal changes (mostly confined to udp_wrapper.c).
//
// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include <cy.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define CY_UDP_POSIX_IFACE_COUNT_MAX 3

#define CY_UDP_POSIX_ASYNC_ERROR_SLOTS 4

/// Dedicated socket IO error counts per redundant interface.
/// There is a single TX socket per redundant interface. All RX sockets are pooled together per interface.
typedef struct cy_udp_posix_stats_socket_t
{
    uint64_t error_count[CY_UDP_POSIX_IFACE_COUNT_MAX];
    cy_us_t  last_error_at;
} cy_udp_posix_stats_socket_t;

/// Statistics exposed for diagnostics and monitoring purposes.
/// The application is not expected to do anything specific with these.
typedef struct cy_udp_posix_stats_t
{
    size_t subject_writer_count;
    size_t subject_reader_count;

    struct cy_udp_posix_stats_mem_t
    {
        size_t   allocated_fragments;
        size_t   allocated_bytes;
        uint64_t oom_count;
    } mem;

    uint64_t message_loss_count;

    cy_udp_posix_stats_socket_t sock_tx;
    cy_udp_posix_stats_socket_t sock_rx;
} cy_udp_posix_stats_t;

/// The default factory that automatically assigns the node parameters that fit most applications:
/// - A semi-random EUI-64.
/// - The local interfaces are chosen per the defaults configured on the local system.
/// - The TX queue capacity is set to a reasonable large value.
cy_platform_t* cy_udp_posix_new(void);

/// A manual alternative that allows specifying the exact iface addresses etc.
/// Unused interfaces should have zero addresses; to parse IP address strings see cy_udp_parse_iface_address().
/// Returns NULL on error.
cy_platform_t* cy_udp_posix_new_manual(const uint64_t uid,
                                       const uint32_t local_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX],
                                       const size_t   tx_queue_capacity);

/// The default home is the fixed-length zero-padded lowercase hex UID (16 lowercase digits); e.g., `0123456789abcdef`.
/// Optionally, a prefix can be added, which will be prepended to the UID via a `/`; e.g., `my_node/0123456789abcdef`;
/// NULL is accepted as an empty prefix.
/// Every node must have a nonempty home and every home should be unique in the network.
/// The string reference is valid until the next invocation of this function (thread-local static).
cy_str_t cy_udp_posix_home(const cy_platform_t* const base, const char* const prefix);

/// The default namespace is read from the CYPHAL_NAMESPACE environment variable; if not set, empty namespace is used.
/// The string reference is valid until the environment is modified (typically until the end of the process lifetime).
cy_str_t cy_udp_posix_namespace(void);

cy_udp_posix_stats_t cy_udp_posix_stats(const cy_platform_t* base);

/// Requires the Cy instance to be unlinked first and all Cy-allocated resources freed.
void cy_udp_posix_destroy(cy_platform_t* const base);

/// The same time base is used for all Cy instances tied to this platform layer.
/// This is simply the count of microseconds sampled via clock_gettime(CLOCK_MONOTONIC).
cy_us_t cy_udp_posix_now(void);

/// Convert an interface address from string to binary representation; e.g., "127.0.0.1" --> 0x7F000001.
/// Returns zero if the input is not valid.
uint32_t cy_udp_parse_iface_address(const char* const address);

#ifdef __cplusplus
}
#endif
