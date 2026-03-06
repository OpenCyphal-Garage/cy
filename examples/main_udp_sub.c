#include <cy.h>
#include <cy_udp_posix.h>
#include <eui64.h>
#include "arg_kv.h"
#include "hexdump.h"
#include <time.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define KILO 1000L
#define MEGA (KILO * 1LL * KILO)

struct config_subscription_t
{
    const char* name;
    bool        ordered;
};

struct config_t
{
    uint32_t iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX];
    uint64_t local_uid;
    size_t   tx_queue_capacity;

    size_t                        sub_count;
    struct config_subscription_t* subs;
};

static struct config_t load_config(const int argc, const char* const argv[])
{
    struct config_t cfg = {
        .local_uid         = eui64_semirandom(),
        .tx_queue_capacity = 1000,
        .sub_count         = 0,
        .subs              = calloc((size_t)(argc - 1), sizeof(struct config_subscription_t)),
    };
    size_t   iface_count = 0;
    arg_kv_t arg;
    while ((arg = arg_kv_next(argc, argv)).key_hash != 0) {
        assert(arg.value != NULL);
        if ((arg_kv_hash("iface") == arg.key_hash) && (iface_count < CY_UDP_POSIX_IFACE_COUNT_MAX)) {
            cfg.iface_address[iface_count++] = cy_udp_parse_iface_address(arg.value);
        } else if (arg_kv_hash("uid") == arg.key_hash) {
            cfg.local_uid = strtoull(arg.value, NULL, 0);
        } else if (arg_kv_hash("txq") == arg.key_hash) {
            cfg.tx_queue_capacity = strtoul(arg.value, NULL, 0);
        } else if ((arg_kv_hash("sub") == arg.key_hash) || (arg_kv_hash("subord") == arg.key_hash)) {
            struct config_subscription_t* x = NULL;
            for (size_t i = 0; i < cfg.sub_count; i++) {
                if (strcmp(cfg.subs[i].name, arg.value) == 0) {
                    x = &cfg.subs[i];
                }
            }
            x          = (x == NULL) ? &cfg.subs[cfg.sub_count++] : x;
            x->name    = arg.value;
            x->ordered = arg_kv_hash("subord") == arg.key_hash;
        } else {
            (void)fprintf(stderr, "Unexpected key #%zu: '%s'\n", arg.index, arg.key);
            exit(1);
        }
    }
    // Print the actual configs we're using.
    (void)fprintf(stderr, "ifaces:");
    for (size_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        (void)fprintf(stderr, " 0x%08jx", (uintmax_t)cfg.iface_address[i]);
    }
    (void)fprintf(stderr, "\nuid: 0x%016jx\n", (uintmax_t)cfg.local_uid);
    (void)fprintf(stderr, "tx_queue_frames: %zu\n", cfg.tx_queue_capacity);
    (void)fprintf(stderr, "subscriptions:\n");
    for (size_t i = 0; i < cfg.sub_count; i++) {
        (void)fprintf(stderr, "\t%s\n", cfg.subs[i].name);
    }
    (void)fprintf(stderr, "---\n");
    return cfg;
}

static void on_message(cy_future_t* const subscriber)
{
    const cy_arrival_t arrival = cy_arrival_move(subscriber);
    if (arrival.message.content == NULL) {
        return;
    }

    const size_t  payload_size = cy_message_size(arrival.message.content);
    unsigned char payload_copy[payload_size];
    cy_message_read(arrival.message.content, 0, payload_size, payload_copy);
    char* const                 dump  = hexdump(payload_size, payload_copy, 32);
    const cy_topic_t* const     topic = cy_topic_find_by_hash(arrival.breadcrumb.cy, arrival.breadcrumb.topic_hash);
    const cy_substitution_set_t substitutions = cy_subscriber_substitutions(subscriber, topic);
    const char* const           topic_name    = (topic != NULL) ? cy_topic_name(topic).str : "<unknown>";
    (void)fprintf(stderr,
                  "💬 ts=%09ju sz=%06zu sbt=%zu topic='%s'\n%s\n",
                  (uintmax_t)arrival.message.timestamp,
                  payload_size,
                  substitutions.count,
                  topic_name,
                  (dump != NULL) ? dump : "<hexdump failed>");
    free(dump);
    // Optionally, send a response to the publisher of this message.
    // The stack knows the identity of the publisher and can deliver a response directly to it.
    // It is possible to stream multiple responses for a single message (the breadcrumb can be copied).
    if ((rand() % 2) == 0) {
        cy_breadcrumb_t breadcrumb = arrival.breadcrumb;
        const cy_err_t  err        = cy_respond(&breadcrumb, // Using best-effort delivery in this example.
                                        arrival.message.timestamp + MEGA,
                                        (cy_bytes_t){ .size = 2, .data = ":3" });
        if (err != CY_OK) {
            (void)fprintf(stderr, "cy_respond: %jd\n", (intmax_t)err);
        }
    }
    cy_message_refcount_dec(arrival.message.content);
}

int main(const int argc, const char* const argv[])
{
    srand((unsigned)time(NULL));
    const struct config_t cfg = load_config(argc, argv);

    // Set up the platform layer that connects Cy to the underlying transport and OS.
    // This is the only part of the code that is platform-specific; the rest is all portable Cy API usage.
    cy_platform_t* const platform = cy_udp_posix_new(cfg.local_uid, cfg.iface_address, cfg.tx_queue_capacity);
    if (platform == NULL) {
        (void)fprintf(stderr, "cy_udp_posix_new\n");
        return 1;
    }

    // Set up the node instance.
    cy_t* const cy = cy_new(platform);
    if (cy == NULL) {
        (void)fprintf(stderr, "cy_new\n");
        return 1;
    }

    // Create subscribers.
    cy_future_t* subscribers[cfg.sub_count];
    for (size_t i = 0; i < cfg.sub_count; i++) {
        subscribers[i] = cfg.subs[i].ordered ? cy_subscribe_ordered(cy, cy_str(cfg.subs[i].name), MEGA, MEGA)
                                             : cy_subscribe(cy, cy_str(cfg.subs[i].name), MEGA);
        if (subscribers[i] == NULL) {
            (void)fprintf(stderr, "cy_subscribe(_ordered): NULL\n");
            return 1;
        }
        cy_future_callback_set(subscribers[i], on_message);
    }

    // Spin the event loop.
    while (true) {
        const cy_err_t err_spin = cy_spin_until(cy, cy_now(cy) + MEGA);
        if (err_spin != CY_OK) {
            (void)fprintf(stderr, "cy_udp_posix_spin_once: %jd\n", (intmax_t)err_spin);
            break;
        }
    }
    return 0;
}
