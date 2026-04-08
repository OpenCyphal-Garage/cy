//                            ____                   ______            __          __
//                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
//                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
//                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
//                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
//                             /_/                     /____/_/
//
// A cy_can_vtable_t implementation for GNU/Linux SocketCAN.
// This module is only usable on GNU/Linux (and potentially some RTOS that implement SocketCAN-like APIs).
//
// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#pragma once

#include "cy_can.h"

#ifdef __cplusplus
extern "C"
{
#endif

/// Create a SocketCAN-backed CAN platform instance bound to the given interface names (e.g., "can0", "can1").
/// CAN FD is auto-detected from the bound interfaces; if any interface is classic-CAN-only, all traffic uses classic.
/// Returns NULL on failure (e.g., interface not found, socket error).
cy_platform_t* cy_can_socketcan_new(const uint_least8_t iface_count,
                                    const char* const   iface_names[],
                                    const size_t        tx_queue_capacity);

void cy_can_socketcan_destroy(cy_platform_t* const base);

#ifdef __cplusplus
}
#endif
