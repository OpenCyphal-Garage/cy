// Subscribes to a legacy UAVCAN v0 / DroneCAN message type over SocketCAN and prints received payloads as hexdumps.

#include <cy.h>
#include <cy_can.h>
#include <cy_can_socketcan.h>

#include "hexdump.h"

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static void on_message(cy_can_v0_subscription_t* const subscription,
                       const cy_us_t                   timestamp,
                       const cy_prio_t                 priority,
                       const uint_least8_t             source_node_id,
                       const uint_least8_t             transfer_id,
                       const cy_bytes_t                payload)
{
    (void)subscription;
    char* const dump = hexdump(payload.size, payload.data, 32U);
    (void)printf("ts=%.6f prio=%d src=%u tid=%u size=%zu\n%s\n",
                 1e-6 * (double)timestamp,
                 (int)priority,
                 (unsigned)source_node_id,
                 (unsigned)transfer_id,
                 payload.size,
                 (dump != NULL) ? dump : "<hexdump failed>");
    (void)fflush(stdout);
    free(dump);
}

int main(const int argc, const char* const argv[])
{
    if ((argc < 3) || (argc > 6)) {
        goto usage;
    }
    const char* const iface_names[1]      = { argv[1] };
    const uint16_t    data_type_id        = (uint16_t)atoi(argv[2]);
    const uint16_t    crc_seed            = (argc > 3) ? (uint16_t)atoi(argv[3]) : UINT16_MAX;
    const size_t      extent              = (argc > 4) ? (size_t)atoi(argv[4]) : 1024U;
    const cy_us_t     transfer_id_timeout = (argc > 5) ? (cy_us_t)atoll(argv[5]) : -1;

    cy_platform_t* const platform = cy_can_socketcan_new(1U, iface_names, 1000U);
    if (platform == NULL) {
        (void)fprintf(stderr, "cy_can_socketcan_new\n");
        return 1;
    }

    cy_t* const cy = cy_new(platform, cy_str("example_dronecan_echo"), cy_str(getenv("CYPHAL_NAMESPACE")));
    if (cy == NULL) {
        (void)fprintf(stderr, "cy_new\n");
        cy_can_socketcan_destroy(platform);
        return 1;
    }

    cy_can_v0_subscription_t* const sub =
      cy_can_v0_subscribe(platform, data_type_id, crc_seed, extent, transfer_id_timeout);
    if (sub == NULL) {
        (void)fprintf(stderr, "cy_can_v0_subscribe failed\n");
        cy_destroy(cy);
        cy_can_socketcan_destroy(platform);
        return 1;
    }
    cy_can_v0_subscription_callback_set(sub, on_message);

    (void)fprintf(stderr,
                  "Listening for DroneCAN messages: dtid=%" PRIu16 ", crc=%" PRIu16 ", extent=%zu, tid_timeout=%" PRId64
                  " us\n",
                  data_type_id,
                  crc_seed,
                  extent,
                  transfer_id_timeout);

    while (true) {
        const cy_err_t err = cy_spin_until(cy, cy_now(cy) + 1000000);
        if (err != CY_OK) {
            (void)fprintf(stderr, "cy_spin_until: %d\n", err);
            break;
        }
    }

    cy_can_v0_unsubscribe(sub);
    cy_destroy(cy);
    cy_can_socketcan_destroy(platform);
    return 1;

usage:
    (void)fprintf(stderr,
                  "Usage: %s <socketcan_ifname> <data_type_id> [crc_seed=65535] [extent=1024] "
                  "[transfer_id_timeout_us=-1]\n",
                  argv[0]);
    return 1;
}
