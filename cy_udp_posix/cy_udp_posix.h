///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// A Cy platform layer for POSIX-like OSes using standard BSD sockets and libUDPard for Cyphal over UDP.
/// It can be adapted to other socket-based APIs with minimal changes (mostly confined to udp_wrapper.c).
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include <cy.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define CY_UDP_POSIX_IFACE_COUNT_MAX 3

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

    struct cy_udp_posix_stats_tx_t
    {
        uint64_t socket_errors[CY_UDP_POSIX_IFACE_COUNT_MAX];
        cy_us_t  last_error_at;
    } tx;

    struct cy_udp_posix_stats_rx_t
    {
        uint64_t socket_errors[CY_UDP_POSIX_IFACE_COUNT_MAX];
        cy_us_t  last_error_at;
    } rx;

    struct cy_udp_posix_stats_cy_async_err_t
    {
        uint16_t line; ///< Zero if unused, otherwise contains the line number in cy.c.
        uint64_t count;
        cy_us_t  last_at;
    } cy_async_errors[4];
} cy_udp_posix_stats_t;

/// Unused interfaces should have zero addresses; to parse IP address strings see udp_wrapper_parse_iface_address().
/// Returns NULL on error.
cy_platform_t* cy_udp_posix_new(const uint64_t uid,
                                const uint32_t local_iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX],
                                const size_t   tx_queue_capacity);

/// A shortcut constructor helper that automatically assigns the node parameters that fit most applications:
/// - A semi-random EUI-64: a few of the most-significant bits are host-specific, the rest are random.
/// - The local interfaces are chosen per the defaults configured on the local system.
/// - The TX queue capacity is set to a reasonable large value.
cy_platform_t* cy_udp_posix_new_auto(void);

/// The same time base is used for all Cy instances tied to this platform layer.
/// This is simply the count of microseconds sampled via clock_gettime(CLOCK_MONOTONIC).
cy_us_t cy_udp_posix_now(void);

/// The default home is the fixed-length zero-padded lowercase hex UID (16 lowercase digits). E.g., `0123456789abcdef`.
/// The string lifetime is tied to the platform instance.
wkv_str_t cy_udp_posix_default_home(const cy_platform_t* self);

/// The default namespace is read from the CYPHAL_NAMESPACE environment variable; if not set, empty namespace is used.
/// The string lifetime is tied to the platform instance.
wkv_str_t cy_udp_posix_default_namespace(const cy_platform_t* self);

cy_udp_posix_stats_t cy_udp_posix_stats(const cy_platform_t* self);

void cy_udp_posix_destroy(cy_platform_t* const self);

#ifdef __cplusplus
}
#endif
