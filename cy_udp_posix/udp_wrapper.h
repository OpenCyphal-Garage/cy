///                            ____                   ______            __          __
///                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
///                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
///                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
///                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
///                             /_/                     /____/_/
///
/// This module implements the platform-specific implementation of the UDP transport. On a conventional POSIX system
/// this would be a thin wrapper around the standard Berkeley sockets API. On a bare-metal system this would be
/// a thin wrapper around the platform-specific network stack, such as LwIP, or a custom solution.
///
/// Having the interface extracted like this helps better illustrate the surface of the networking API required
/// by LibUDPard, which is minimal. This also helps with porting to new platforms.
///
/// All addresses and values used in this API are in the host-native byte order.
/// For example, 127.0.0.1 is represented as 0x7F000001 always.
///
/// This software is distributed under the terms of the MIT License.
/// Copyright (C) OpenCyphal Development Team  <opencyphal.org>
/// Copyright Amazon.com Inc. or its affiliates.
/// SPDX-License-Identifier: MIT
/// Author: Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// These definitions are highly platform-specific.
/// Note that LibUDPard does not require the same socket to be usable for both transmission and reception.
struct udp_wrapper_tx_t
{
    int fd;
};
struct udp_wrapper_rx_t
{
    int fd;
    // dgram accepted if iface index matches AND (src adr OR src port differ). The latter is to discard own traffic.
    uint32_t allow_iface_index;
    uint32_t deny_source_address;
    uint16_t deny_source_port;
};

/// Helpers for constructing uninitialized handles.
struct udp_wrapper_tx_t udp_wrapper_tx_new(void);
struct udp_wrapper_rx_t udp_wrapper_rx_new(void);

/// Return false unless the handle has been successfully initialized and not yet closed.
bool udp_wrapper_tx_is_initialized(const struct udp_wrapper_tx_t* const self);
bool udp_wrapper_rx_is_initialized(const struct udp_wrapper_rx_t* const self);

/// Initialize a TX socket for use with LibUDPard.
/// The local iface address is used to specify the egress interface for multicast traffic.
/// Per LibUDPard design, there is one TX socket per redundant interface, so the application needs to invoke
/// this function once per interface.
///
/// The local port will be chosen automatically (ephemeral); if the local_port pointer is not NULL, the actual port
/// number will be stored there. This should be used later to drop datagrams looped back from the TX socket to the
/// local RX sockets by comparing the origin endpoint of the received datagrams with the local port & iface address
/// of the TX socket. I am not sure if there is a better way of ignoring own datagrams.
///
/// On error returns a negative error code.
int16_t udp_wrapper_tx_init(struct udp_wrapper_tx_t* const self,
                            const uint32_t                 local_iface_address,
                            uint16_t* const                local_port);

/// Send a datagram to the specified endpoint without blocking using the specified IP DSCP field value.
/// A real-time embedded system should normally accept a transmission deadline here for the networking stack.
/// Returns 1 on success, 0 if the socket is not ready for sending, or a negative error code.
int16_t udp_wrapper_tx_send(struct udp_wrapper_tx_t* const self,
                            const uint32_t                 remote_address,
                            const uint16_t                 remote_port,
                            const uint8_t                  dscp,
                            const size_t                   payload_size,
                            const void* const              payload);

/// No effect if the argument is invalid.
/// This function is guaranteed to invalidate the handle.
void udp_wrapper_tx_close(struct udp_wrapper_tx_t* const self);

/// Initialize an RX socket for use with LibUDPard, for subscription to subjects or for RPC traffic.
/// The socket will be bound to the specified multicast group and port.
/// Most socket APIs, in particular the Berkeley sockets, require the local iface address to be known,
/// because it is used to decide which egress port to send IGMP membership reports over.
/// Dgrams whose source port matches the specified deny_source_port will be ignored; this is to ignore own tx dgrams.
/// On error returns a negative error code.
int16_t udp_wrapper_rx_init(struct udp_wrapper_rx_t* const self,
                            const uint32_t                 local_iface_address,
                            const uint32_t                 multicast_group,
                            const uint16_t                 remote_port,
                            const uint16_t                 deny_source_port);

/// Read one datagram from the socket without blocking.
/// The size of the destination buffer is specified in inout_payload_size; it is updated to the actual size of the
/// received datagram upon return.
///
/// The remote address and port are reported to allow the reader filter out own datagrams that were looped back
/// from the TX socket to the local RX sockets.
///
/// Returns:
///     1 on success
///     0 if the socket is not ready for reading OR if the received dgram is a looped back own datagram
///     negative error code
int16_t udp_wrapper_rx_receive(struct udp_wrapper_rx_t* const self,
                               size_t* const                  inout_payload_size,
                               void* const                    out_payload);

/// No effect if the argument is invalid.
/// This function is guaranteed to invalidate the handle.
void udp_wrapper_rx_close(struct udp_wrapper_rx_t* const self);

/// Suspend execution until the expiration of the timeout (in microseconds) or until any of the specified handles
/// become ready for reading (the RX group) or writing (the TX group). Upon completion, handle pointers that are
/// ready to read/write will be left intact, while those that are NOT ready will be set to NULL.
/// The function may return earlier than the timeout even if no handles are ready.
/// On error returns a negative error code.
///
/// The recommended usage pattern is to keep parallel arrays of handle pointers and some context data, e.g.:
///
///     struct udp_wrapper_tx_t* tx_handles[UDPARD_IFACE_COUNT_MAX];
///     struct udp_wrapper_rx_t* rx_handles[max_rx_handles];
///     struct void* rx_context[max_rx_handles];                // Parallel array of context data.
///     int16_t err = udp_wrapper_wait(timeout_us, UDPARD_IFACE_COUNT_MAX, tx_handles, max_rx_handles, rx_handles);
///     // Then handle the results.
int16_t udp_wrapper_wait(const int64_t                   timeout_us,
                         const size_t                    tx_count,
                         struct udp_wrapper_tx_t** const tx,
                         const size_t                    rx_count,
                         struct udp_wrapper_rx_t** const rx);

/// Convert an interface address from string to binary representation; e.g., "127.0.0.1" --> 0x7F000001.
/// Returns zero if the address is not recognized.
uint32_t udp_wrapper_parse_iface_address(const char* const address);

#ifdef __cplusplus
}
#endif
