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

/// These definitions are highly platform-specific; the application normally should not rely on the internal fields.
typedef struct udp_wrapper_t
{
    int    fd;
    size_t iface_index;
} udp_wrapper_t;

/// Helpers for constructing uninitialized handles.
udp_wrapper_t udp_wrapper_new(void);

/// Return false unless the handle has been successfully opened and not yet closed.
bool udp_wrapper_is_open(const udp_wrapper_t* const self);

/// Initialize a socket for use with LibUDPard for transmission of datagrams to arbitrary remote endpoints,
/// including multicast, and for the reception of unicast P2P traffic.
/// The local iface address is used to specify the egress interface for multicast traffic sent over this socket.
/// Per LibUDPard design, there is one TX socket per redundant interface, so the application needs to invoke
/// this function once per interface.
/// The local port is chosen for the socket automatically and returned via out_local_port.
/// On error returns a negative errno.
int16_t udp_wrapper_open_unicast(udp_wrapper_t* const self,
                                 const uint32_t       local_iface_address,
                                 uint16_t* const      out_local_port);

/// Initialize an RX socket for use with LibUDPard, for listening to multicast groups.
/// The socket will be bound to the specified multicast endpoint (group and port).
/// The local iface address specifies which egress port to send IGMP membership reports over.
/// On error returns a negative error code.
int16_t udp_wrapper_open_multicast(udp_wrapper_t* const self,
                                   const uint32_t       local_iface_address,
                                   const uint32_t       multicast_group,
                                   const uint16_t       remote_port);

/// No effect if the argument is invalid.
/// This function is guaranteed to invalidate the handle.
void udp_wrapper_close(udp_wrapper_t* const self);

/// Send a datagram to the specified endpoint without blocking using the specified IP DSCP field value.
/// A real-time embedded system should normally accept a transmission deadline here for the networking stack.
/// Returns 1 on success, 0 if the socket is not ready for sending, or a negative error code.
int16_t udp_wrapper_send(udp_wrapper_t* const self,
                         const uint32_t       remote_address,
                         const uint16_t       remote_port,
                         const uint8_t        dscp,
                         const size_t         payload_size,
                         const void* const    payload);

/// Read one datagram from the socket without blocking.
/// The size of the destination buffer is specified in inout_payload_size; it is updated to the actual size of the
/// received datagram upon return.
/// The returned data may have originated from the local tx socket; filtering may be needed.
/// It is guaranteed that the returned datagram has arrived via the local interface set when opening the socket.
/// Returns:
///     1 on success
///     0 if the socket is not ready for reading OR if the received dgram is a looped back own datagram
///     negative error code
int16_t udp_wrapper_receive(udp_wrapper_t* const self,
                            size_t* const        inout_payload_size,
                            void* const          out_payload,
                            uint32_t* const      out_src_address,
                            uint16_t* const      out_src_port);

/// Suspend execution until the expiration of the timeout (in microseconds) or until any of the specified handles
/// become ready for reading (the RX group) or writing (the TX group). Upon completion, handle pointers that are
/// ready to read/write will be left intact, while those that are NOT ready will be set to NULL.
/// The function may return earlier than the timeout even if no handles are ready.
/// The same handle can appear in both TX and RX groups.
/// On error returns a negative error code.
///
/// The recommended usage pattern is to keep parallel arrays of handle pointers and some context data, e.g.:
///
///     udp_wrapper_tx_t* tx_handles[UDPARD_IFACE_COUNT_MAX];
///     udp_wrapper_rx_t* rx_handles[max_rx_handles];
///     void* rx_context[max_rx_handles];                // Parallel array of context data.
///     int16_t err = udp_wrapper_wait(timeout_us, UDPARD_IFACE_COUNT_MAX, tx_handles, max_rx_handles, rx_handles);
///     // Then handle the results.
int16_t udp_wrapper_wait(const int64_t         timeout_us,
                         const size_t          tx_count,
                         udp_wrapper_t** const tx,
                         const size_t          rx_count,
                         udp_wrapper_t** const rx);

/// Convert an interface address from string to binary representation; e.g., "127.0.0.1" --> 0x7F000001.
/// Returns zero if the address is not recognized.
uint32_t udp_wrapper_parse_iface_address(const char* const address);

#ifdef __cplusplus
}
#endif
