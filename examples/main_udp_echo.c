// Subscribes to a topic and prints received messages as ASCII hexdumps.
// Hint: use pattern subscriptions to receive data from multiple topics concurrently; e.g., `>` to receive everything.

#include <cy.h>
#include <cy_udp_posix.h>

#include "hexdump.h"

#include <stdio.h>
#include <stdlib.h>

static void on_message(cy_future_t* const subscriber)
{
    if (!cy_future_done(subscriber)) {
        (void)fprintf(stderr, "💥 transient subscriber error: %d\n", cy_future_error(subscriber));
        return;
    }

    // Fetch the received message.
    const cy_arrival_t arrival = cy_arrival_move(subscriber);

    // Read the message and make a human-friendly ASCII hexdump.
    const size_t  payload_size = cy_message_size(arrival.message.content);
    unsigned char payload_copy[(payload_size > 0U) ? payload_size : 1U];
    const void*   payload = NULL;
    if (payload_size > 0U) {
        (void)cy_message_read(arrival.message.content, 0, payload_size, payload_copy);
        payload = payload_copy;
    }
    char* const dump = hexdump(payload_size, payload, 32U);

    // Fetch the message metadata.
    const cy_topic_t* const topic      = cy_topic_find_by_hash(arrival.breadcrumb.cy, arrival.breadcrumb.topic_hash);
    const char* const       topic_name = cy_topic_name(topic).str;
    const double            timestamp  = 1e-6 * (double)arrival.message.timestamp;

    // Print the message.
    (void)printf("📩 '%s' at %.3f %zu bytes\n%s\n", topic_name, timestamp, payload_size, dump);
    (void)fflush(stdout);

    // Clean up.
    free(dump);
    cy_message_refcount_dec(arrival.message.content);
}

int main(const int argc, const char* const argv[])
{
    if (argc != 2) { // TODO: subscribe to multiple patterns
        (void)fprintf(stderr, "Usage: %s <topic>\n", argv[0]);
        return 1;
    }

    cy_platform_t* const platform = cy_udp_posix_new();
    if (platform == NULL) {
        (void)fprintf(stderr, "cy_udp_posix_new\n");
        return 1;
    }
    cy_t* const cy = cy_new(platform, cy_udp_posix_home(platform, "udp_echo"), cy_udp_posix_namespace());
    if (cy == NULL) {
        (void)fprintf(stderr, "cy_new\n");
        return 1;
    }

    cy_future_t* const sub = cy_subscribe(cy, cy_str(argv[1]), 1024U);
    if (sub == NULL) {
        (void)fprintf(stderr, "cy_subscribe\n");
        return 1;
    }
    cy_future_callback_set(sub, on_message);

    while (true) {
        const cy_err_t err = cy_spin_once(cy);
        if (err != CY_OK) {
            (void)fprintf(stderr, "cy_spin_once: %d\n", err);
            return 1;
        }
    }
}
