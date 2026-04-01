//                            ____                   ______            __          __
//                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
//                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
//                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
//                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
//                             /_/                     /____/_/
//
// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

// Feature test macros must come before any system headers.
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include "cy_can_socketcan.h"
#include <cy_platform.h>
#include <canard.h>

#define RAPIDHASH_COMPACT
#include <rapidhash.h>

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <time.h>
#include <poll.h>

#include <sys/socket.h>
#include <sys/ioctl.h>
#include <net/if.h>
#include <linux/can.h>
#include <linux/can/raw.h>

#if CY_CONFIG_TRACE
#include <stdio.h>
#include <stdarg.h>

void cy_trace(cy_t* const         cy,
              const char* const   file,
              const uint_fast16_t line,
              const char* const   func,
              const char* const   format,
              ...)
{
    (void)cy;
    struct timespec ts;
    (void)clock_gettime(CLOCK_MONOTONIC, &ts);
    const char* fn = strrchr(file, '/');
    fn             = (fn != NULL) ? (fn + 1) : file;
    (void)fprintf(
      stderr, "CY_CAN %05ld.%06ld %s:%u:%s ", (long)ts.tv_sec, ts.tv_nsec / 1000L, fn, (unsigned)line, func);
    va_list args;
    va_start(args, format);
    (void)vfprintf(stderr, format, args);
    va_end(args);
    (void)fputc('\n', stderr);
    (void)fflush(stderr);
}
#endif

// =====================================================================================================================

typedef struct
{
    int           sock_fd[CANARD_IFACE_COUNT];
    uint_least8_t iface_count;
    bool          fd_capable;
    uint64_t      prng_state;
} socketcan_t;

static cy_us_t socketcan_now(void)
{
    struct timespec ts;
    (void)clock_gettime(CLOCK_MONOTONIC, &ts);
    return ((cy_us_t)ts.tv_sec * 1000000LL) + (cy_us_t)(ts.tv_nsec / 1000L);
}

// =====================================================================================================================
// VTABLE IMPLEMENTATION

static bool v_tx_classic(void* const         user,
                         const uint_least8_t iface_index,
                         const uint32_t      can_id,
                         const void* const   data,
                         const uint_least8_t len)
{
    const socketcan_t* const self = (const socketcan_t*)user;
    assert(iface_index < self->iface_count);
    struct can_frame frame = { .can_id = can_id | CAN_EFF_FLAG, .can_dlc = len };
    if ((data != NULL) && (len > 0)) {
        (void)memcpy(frame.data, data, (len <= 8) ? len : 8);
    }
    const ssize_t res = write(self->sock_fd[iface_index], &frame, sizeof(frame));
    return res == (ssize_t)sizeof(frame);
}

static bool v_tx_fd(void* const         user,
                    const uint_least8_t iface_index,
                    const uint32_t      can_id,
                    const void* const   data,
                    const uint_least8_t len)
{
    const socketcan_t* const self = (const socketcan_t*)user;
    assert(iface_index < self->iface_count);
    struct canfd_frame frame = { .can_id = can_id | CAN_EFF_FLAG, .len = len, .flags = CANFD_FDF };
    if ((data != NULL) && (len > 0)) {
        (void)memcpy(frame.data, data, (len <= 64) ? len : 64);
    }
    const ssize_t res = write(self->sock_fd[iface_index], &frame, sizeof(frame));
    return res == (ssize_t)sizeof(frame);
}

static bool v_rx(void* const         user,
                 cy_can_rx_t* const  out_frame,
                 const cy_us_t       deadline,
                 const uint_least8_t tx_pending_iface_bitmap)
{
    socketcan_t* const self = (socketcan_t*)user;
    struct pollfd      fds[CANARD_IFACE_COUNT];
    for (uint_least8_t i = 0; i < self->iface_count; i++) {
        fds[i].fd      = self->sock_fd[i];
        fds[i].events  = POLLIN;
        fds[i].revents = 0;
        if (((tx_pending_iface_bitmap >> i) & 1U) != 0) { // NOLINT(*-signed-bitwise)
            fds[i].events |= POLLOUT;                     // NOLINT(*-signed-bitwise)
        }
    }
    const cy_us_t now        = socketcan_now();
    const int     timeout_ms = (deadline > now) ? (int)((deadline - now) / 1000LL) : 0;
    const int     ret        = poll(fds, self->iface_count, timeout_ms);
    if (ret <= 0) {
        return false;
    }
    for (uint_least8_t i = 0; i < self->iface_count; i++) {
        if ((fds[i].revents & POLLIN) == 0) { // NOLINT(*-signed-bitwise)
            continue;
        }
        out_frame->iface_index = i;
        out_frame->timestamp   = socketcan_now(); // embedded systems would typically sample the hardware clock
        if (self->fd_capable) {
            struct canfd_frame frame;
            const ssize_t      n = read(self->sock_fd[i], &frame, sizeof(frame));
            if (n < (ssize_t)sizeof(struct can_frame)) {
                continue;
            }
            out_frame->can_id = frame.can_id & CAN_EFF_MASK;
            out_frame->fd     = ((size_t)n == sizeof(struct canfd_frame));
            out_frame->len    = out_frame->fd ? frame.len : ((struct can_frame*)&frame)->can_dlc;
            if (out_frame->len > 64) {
                out_frame->len = 64;
            }
            (void)memcpy(out_frame->data, frame.data, out_frame->len);
        } else {
            struct can_frame frame;
            const ssize_t    n = read(self->sock_fd[i], &frame, sizeof(frame));
            if (n < (ssize_t)sizeof(frame)) {
                continue;
            }
            out_frame->can_id = frame.can_id & CAN_EFF_MASK;
            out_frame->fd     = false;
            out_frame->len    = frame.can_dlc;
            if (out_frame->len > 8) {
                out_frame->len = 8;
            }
            (void)memcpy(out_frame->data, frame.data, out_frame->len);
        }
        return true;
    }
    return false;
}

static cy_us_t v_now(void* const user)
{
    (void)user;
    return socketcan_now();
}

static void* v_realloc(void* const user, void* const ptr, const size_t size)
{
    (void)user;
    if (size > 0) {
        return realloc(ptr, size);
    }
    free(ptr);
    return NULL;
}

static uint64_t v_random(void* const user)
{
    socketcan_t* const self = (socketcan_t*)user;
    self->prng_state += 0xA0761D6478BD642FULL;
    return rapidhash_withSeed(&self->prng_state, sizeof(uint64_t), (uintptr_t)self);
}

static const cy_can_vtable_t socketcan_vtable_fd      = { .tx_classic = v_tx_classic,
                                                          .tx_fd      = v_tx_fd,
                                                          .rx         = v_rx,
                                                          .now        = v_now,
                                                          .realloc    = v_realloc,
                                                          .random     = v_random };
static const cy_can_vtable_t socketcan_vtable_classic = { .tx_classic = v_tx_classic,
                                                          .tx_fd      = NULL, // No FD support.
                                                          .rx         = v_rx,
                                                          .now        = v_now,
                                                          .realloc    = v_realloc,
                                                          .random     = v_random };

// =====================================================================================================================
// PUBLIC API

cy_platform_t* cy_can_socketcan_new(const uint_least8_t iface_count,
                                    const char*         iface_names[],
                                    const size_t        tx_queue_capacity)
{
    if ((iface_count == 0) || (iface_count > CANARD_IFACE_COUNT) || (iface_names == NULL)) {
        return NULL;
    }
    socketcan_t* const self = (socketcan_t*)calloc(1, sizeof(socketcan_t));
    if (self == NULL) {
        return NULL;
    }
    self->iface_count = iface_count;
    self->fd_capable  = true; // Assume FD until proven otherwise.
    for (uint_least8_t i = 0; i < CANARD_IFACE_COUNT; i++) {
        self->sock_fd[i] = -1;
    }

    // Seed the PRNG from best available source.
    {
        const int    fd = open("/dev/urandom", O_RDONLY);
        const size_t sz = sizeof(self->prng_state);
        const bool   ok = (fd >= 0) && (read(fd, &self->prng_state, sz) == (ssize_t)sz);
        (void)close(fd);
        if (!ok) {
            self->prng_state = ((uint64_t)socketcan_now()) ^ (uint64_t)time(NULL) ^ ((uint64_t)(uintptr_t)self);
        }
    }

    for (uint_least8_t i = 0; i < iface_count; i++) {
        const int sock = socket(PF_CAN, SOCK_RAW, CAN_RAW);
        if (sock < 0) {
            goto fail;
        }
        self->sock_fd[i] = sock;
        // Bind to the named interface.
        struct ifreq ifr;
        (void)memset(&ifr, 0, sizeof(ifr));
        (void)strncpy(ifr.ifr_name, iface_names[i], sizeof(ifr.ifr_name) - 1);
        if (ioctl(sock, SIOCGIFINDEX, &ifr) < 0) {
            goto fail;
        }
        struct sockaddr_can addr;
        (void)memset(&addr, 0, sizeof(addr));
        addr.can_family  = AF_CAN;
        addr.can_ifindex = ifr.ifr_ifindex;
        if (bind(sock, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
            goto fail;
        }
        // Try enabling CAN FD. If it fails on any interface, disable FD for all.
        {
            const int enable = 1;
            if (setsockopt(sock, SOL_CAN_RAW, CAN_RAW_FD_FRAMES, &enable, sizeof(enable)) < 0) {
                self->fd_capable = false;
            }
        }
        // Non-blocking mode.
        {
            const int flags = fcntl(sock, F_GETFL, 0);
            if (flags >= 0) {
                (void)fcntl(sock, F_SETFL, flags | O_NONBLOCK); // NOLINT(*-signed-bitwise)
            }
        }
    }

    const cy_can_vtable_t* const vtable = self->fd_capable ? &socketcan_vtable_fd : &socketcan_vtable_classic;
    cy_platform_t* const         result = cy_can_new(iface_count, tx_queue_capacity, vtable, self);
    if (result == NULL) {
        goto fail;
    }
    return result;

fail:
    for (uint_least8_t i = 0; i < CANARD_IFACE_COUNT; i++) {
        if (self->sock_fd[i] >= 0) {
            (void)close(self->sock_fd[i]);
        }
    }
    free(self);
    return NULL;
}

void cy_can_socketcan_destroy(cy_platform_t* const base)
{
    if (base == NULL) {
        return;
    }
    socketcan_t* const self = (socketcan_t*)cy_can_user(base);
    cy_can_destroy(base);
    for (uint_least8_t i = 0; i < CANARD_IFACE_COUNT; i++) {
        if (self->sock_fd[i] >= 0) {
            (void)close(self->sock_fd[i]);
        }
    }
    free(self);
}
