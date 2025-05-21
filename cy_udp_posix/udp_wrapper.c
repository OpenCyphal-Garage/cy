/// This software is distributed under the terms of the MIT License.
/// Copyright (C) OpenCyphal Development Team  <opencyphal.org>
/// Copyright Amazon.com Inc. or its affiliates.
/// SPDX-License-Identifier: MIT
/// Author: Pavel Kirienko <pavel@opencyphal.org>

#include "udp_wrapper.h"

/// Enable SO_REUSEPORT.
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE // NOLINT(bugprone-reserved-identifier,cert-dcl37-c,cert-dcl51-cpp)
#endif

#include <fcntl.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <ifaddrs.h>
#include <net/if.h>
#include <unistd.h>
#include <poll.h>
#include <errno.h>
#include <limits.h>
#include <stdbool.h>

/// This is the value recommended by the Cyphal/UDP specification.
#define OVERRIDE_TTL 16

/// RFC 2474.
#define DSCP_MAX 63

struct in_pktinfo
{
    unsigned ipi_ifindex;  // incoming ifindex
    uint32_t ipi_spec_dst; // local destination address
    uint32_t ipi_addr;     // header source address
};

static bool is_multicast(const uint32_t address)
{
    return (address & 0xF0000000UL) == 0xE0000000UL; // NOLINT(*-magic-numbers)
}

/// Zero on error, otherwise the interface index. Zero is not a valid interface index.
static uint32_t get_local_iface_index(const uint32_t local_iface_address)
{
    const uint32_t  addr_be = htonl(local_iface_address);
    struct ifaddrs* ifa;
    uint32_t        idx = 0;
    if (getifaddrs(&ifa) == 0) {
        for (struct ifaddrs* it = ifa; it; it = it->ifa_next) {
            if (it->ifa_addr && it->ifa_addr->sa_family == AF_INET) {
                const struct sockaddr_in* const sa = (struct sockaddr_in*)it->ifa_addr;
                if (sa->sin_addr.s_addr == addr_be) {
                    idx = if_nametoindex(it->ifa_name);
                    break;
                }
            }
        }
        freeifaddrs(ifa);
    }
    return idx;
}

struct udp_wrapper_tx_t udp_wrapper_tx_new(void)
{
    return (struct udp_wrapper_tx_t){ .fd = -1 };
}
struct udp_wrapper_rx_t udp_wrapper_rx_new(void)
{
    return (struct udp_wrapper_rx_t){ .fd = -1 };
}

/// Return false unless the handle has been successfully initialized and not yet closed.
bool udp_wrapper_tx_is_initialized(const struct udp_wrapper_tx_t* const self)
{
    return self->fd >= 0;
}
bool udp_wrapper_rx_is_initialized(const struct udp_wrapper_rx_t* const self)
{
    return self->fd >= 0;
}

int16_t udp_wrapper_tx_init(struct udp_wrapper_tx_t* const self,
                            const uint32_t                 local_iface_address,
                            uint16_t* const                local_port)
{
    int16_t res = -EINVAL;
    if ((self != NULL) && (local_iface_address > 0)) {
        self->fd                      = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
        const uint32_t local_iface_be = htonl(local_iface_address);
        const int      ttl            = OVERRIDE_TTL;
        bool           ok             = self->fd >= 0;
        //
        ok = ok && bind(self->fd,
                        (struct sockaddr*)&(struct sockaddr_in){
                          .sin_family = AF_INET,
                          .sin_addr   = { local_iface_be },
                          .sin_port   = 0,
                        },
                        sizeof(struct sockaddr_in)) == 0;
        if (ok && (local_port != NULL)) {
            struct sockaddr_in sa = { 0 };
            socklen_t          al = sizeof(sa);
            ok                    = getsockname(self->fd, (struct sockaddr*)&sa, &al) == 0;
            *local_port           = ntohs(sa.sin_port);
        }
        ok = ok && fcntl(self->fd, F_SETFL, O_NONBLOCK) == 0;
        ok = ok && setsockopt(self->fd, IPPROTO_IP, IP_MULTICAST_TTL, &ttl, sizeof(ttl)) == 0;
        // Specify the egress interface for multicast traffic.
        ok = ok && setsockopt(self->fd, IPPROTO_IP, IP_MULTICAST_IF, &local_iface_be, sizeof(local_iface_be)) == 0;
        if (ok) {
            res = 0;
        } else {
            res = (int16_t)-errno;
            (void)close(self->fd);
            self->fd = -1;
        }
    }
    return res;
}

int16_t udp_wrapper_tx_send(struct udp_wrapper_tx_t* const self,
                            const uint32_t                 remote_address,
                            const uint16_t                 remote_port,
                            const uint8_t                  dscp,
                            const size_t                   payload_size,
                            const void* const              payload)
{
    int16_t res = -EINVAL;
    if ((self != NULL) && (self->fd >= 0) && (remote_address > 0) && (remote_port > 0) && (payload != NULL) &&
        (dscp <= DSCP_MAX)) {
        const int dscp_int = dscp << 2U; // The 2 least significant bits are used for the ECN field.
        (void)setsockopt(self->fd, IPPROTO_IP, IP_TOS, &dscp_int, sizeof(dscp_int)); // Best effort.
        const ssize_t send_result = sendto(
          self->fd,
          payload,
          payload_size,
          MSG_DONTWAIT,
          (struct sockaddr*)&(struct sockaddr_in){
            .sin_family = AF_INET, .sin_addr = { .s_addr = htonl(remote_address) }, .sin_port = htons(remote_port) },
          sizeof(struct sockaddr_in));
        if (send_result == (ssize_t)payload_size) {
            res = 1;
        } else if ((errno == EAGAIN) || (errno == EWOULDBLOCK)) {
            res = 0;
        } else {
            res = (int16_t)-errno;
        }
    }
    return res;
}

void udp_wrapper_tx_close(struct udp_wrapper_tx_t* const self)
{
    if ((self != NULL) && (self->fd >= 0)) {
        (void)close(self->fd);
        self->fd = -1;
    }
}

int16_t udp_wrapper_rx_init(struct udp_wrapper_rx_t* const self,
                            const uint32_t                 local_iface_address,
                            const uint32_t                 multicast_group,
                            const uint16_t                 remote_port,
                            const uint16_t                 deny_source_port)
{
    int16_t res = -EINVAL;
    if ((self != NULL) && (local_iface_address > 0) && is_multicast(multicast_group) && (remote_port > 0)) {
        const int one             = 1;
        self->deny_source_address = local_iface_address;
        self->deny_source_port    = deny_source_port;
        self->allow_iface_index   = get_local_iface_index(local_iface_address);
        self->fd                  = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
        bool ok                   = (self->fd >= 0) && (self->allow_iface_index > 0);
        // Set non-blocking mode.
        ok = ok && (fcntl(self->fd, F_SETFL, O_NONBLOCK) == 0);
        // Allow other applications to use the same Cyphal port as well. This must be done before binding.
        // Failure to do so will make it impossible to run more than one Cyphal/UDP node on the same host.
        ok = ok && (setsockopt(self->fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one)) == 0);
#ifdef SO_REUSEPORT // Linux
        ok = ok && (setsockopt(self->fd, SOL_SOCKET, SO_REUSEPORT, &one, sizeof(one)) == 0);
#endif
        // Request extended metadata on rx so that we could only accept traffic from our own iface.
        ok = ok && (setsockopt(self->fd, IPPROTO_IP, IP_PKTINFO, &one, sizeof(one)) == 0);
        // Binding to the multicast group address is necessary on GNU/Linux: https://habr.com/ru/post/141021/
        // Binding to a multicast address is not allowed on Windows, and it is not necessary there;
        // instead, one should bind to INADDR_ANY with the specific port.
        const struct sockaddr_in bind_addr = {
            .sin_family = AF_INET,
#ifdef _WIN32
            .sin_addr = { .s_addr = INADDR_ANY },
#else
            .sin_addr = { .s_addr = htonl(multicast_group) },
#endif
            .sin_port = htons(remote_port),
        };
        ok = ok && (bind(self->fd, (struct sockaddr*)&bind_addr, sizeof(bind_addr)) == 0);
        // INADDR_ANY in IP_ADD_MEMBERSHIP doesn't actually mean "any", it means "choose one automatically";
        // see https://tldp.org/HOWTO/Multicast-HOWTO-6.html. This is why we have to specify the interface explicitly.
        // This is needed to inform the networking stack of which local interface to use for IGMP membership reports.
        const struct in_addr tuple[2] = { { .s_addr = htonl(multicast_group) },
                                          { .s_addr = htonl(local_iface_address) } };
        ok = ok && (setsockopt(self->fd, IPPROTO_IP, IP_ADD_MEMBERSHIP, &tuple[0], sizeof(tuple)) == 0);
        if (ok) {
            res = 0;
        } else {
            res = (int16_t)-errno;
            (void)close(self->fd);
            self->fd = -1;
        }
    }
    return res;
}

int16_t udp_wrapper_rx_receive(struct udp_wrapper_rx_t* const self,
                               size_t* const                  inout_payload_size,
                               void* const                    out_payload)
{
    int16_t res = -EINVAL;
    if ((self != NULL) && (self->fd >= 0) && (inout_payload_size != NULL) && (out_payload != NULL)) {
        struct sockaddr_in src = { 0 };
        struct iovec       iov = { .iov_base = out_payload, .iov_len = *inout_payload_size };
        char               cbuf[CMSG_SPACE(sizeof(struct in_pktinfo))];
        struct msghdr      msg = { .msg_name       = &src,
                                   .msg_namelen    = sizeof(src),
                                   .msg_iov        = &iov,
                                   .msg_iovlen     = 1,
                                   .msg_control    = cbuf,
                                   .msg_controllen = sizeof(cbuf) };
        const ssize_t      n   = recvmsg(self->fd, &msg, MSG_DONTWAIT);
        if (n >= 0) {
            // locate IP_PKTINFO
            struct in_pktinfo* pi = NULL;
            for (struct cmsghdr* c = CMSG_FIRSTHDR(&msg); c; c = CMSG_NXTHDR(&msg, c)) {
                if (c->cmsg_level == IPPROTO_IP && c->cmsg_type == IP_PKTINFO) {
                    pi = (struct in_pktinfo*)CMSG_DATA(c);
                    break;
                }
            }
            // drop out own traffic and only accept packets from the right iface.
            if (pi == NULL) {
                res = -EIO;
            } else if (pi->ipi_ifindex != self->allow_iface_index) {
                res = 0; // wrong iface -- ignore
            } else if ((ntohl(src.sin_addr.s_addr) == self->deny_source_address) &&
                       (ntohs(src.sin_port) == self->deny_source_port)) {
                res = 0; // own traffic -- ignore
            } else {
                *inout_payload_size = (size_t)n;
                res                 = 1;
            }
        } else if ((errno == EAGAIN) || (errno == EWOULDBLOCK)) {
            res = 0;
        } else {
            res = (int16_t)-errno;
        }
    }
    return res;
}

void udp_wrapper_rx_close(struct udp_wrapper_rx_t* const self)
{
    if ((self != NULL) && (self->fd >= 0)) {
        (void)close(self->fd);
        self->fd = -1;
    }
}

int16_t udp_wrapper_wait(const int64_t                   timeout_us,
                         const size_t                    tx_count,
                         struct udp_wrapper_tx_t** const tx,
                         const size_t                    rx_count,
                         struct udp_wrapper_rx_t** const rx)
{
    int16_t       res         = -EINVAL;
    const size_t  total_count = tx_count + rx_count;
    struct pollfd fds[total_count]; // Violates MISRA-C:2012 Rule 18.8; replace with a fixed limit.
    // IEEE Std 1003.1 requires:
    //
    //  The implementation shall support one or more programming environments in which the width of nfds_t is
    //  no greater than the width of type long.
    //
    // Per C99, the minimum size of "long" is 32 bits, hence we compare against INT32_MAX.
    // OPEN_MAX is not used because it is not guaranteed to be defined nor the limit has to be static.
    if ((tx != NULL) && (rx != NULL) && (total_count > 0) && (total_count <= INT32_MAX)) {
        {
            size_t idx = 0;
            for (; idx < tx_count; idx++) {
                fds[idx].fd     = tx[idx]->fd;
                fds[idx].events = POLLOUT;
            }
            for (; idx < tx_count + rx_count; idx++) {
                fds[idx].fd     = rx[idx - tx_count]->fd;
                fds[idx].events = POLLIN;
            }
        }
        const int64_t timeout_ms = timeout_us / 1000;
        const int poll_result    = poll(fds, (nfds_t)total_count, (int)((timeout_ms > INT_MAX) ? INT_MAX : timeout_ms));
        if (poll_result >= 0) {
            res        = 0;
            size_t idx = 0;
            for (; idx < tx_count; idx++) {
                if ((fds[idx].revents & POLLOUT) == 0) { // NOLINT(*-signed-bitwise)
                    tx[idx] = NULL;
                }
            }
            for (; idx < tx_count + rx_count; idx++) {
                if ((fds[idx].revents & POLLIN) == 0) { // NOLINT(*-signed-bitwise)
                    rx[idx - tx_count] = NULL;
                }
            }
        } else {
            res = (int16_t)-errno;
        }
    }
    return res;
}

uint32_t udp_wrapper_parse_iface_address(const char* const address)
{
    uint32_t out = 0;
    if (address != NULL) {
        struct in_addr addr;
        if (inet_pton(AF_INET, address, &addr) == 1) {
            out = ntohl(addr.s_addr);
        }
    }
    return out;
}
