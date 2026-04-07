#include <cy.h>

#include "example_platform.h"
#include "arg_kv.h"
#include "hexdump.h"
#include <time.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
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
    size_t                        sub_count;
    struct config_subscription_t* subs;
};

static struct config_t load_config(const int argc, char* const argv[])
{
    const size_t    config_capacity = (size_t)((argc > 1) ? (argc - 1) : 1);
    struct config_t cfg = { .sub_count = 0, .subs = calloc(config_capacity, sizeof(struct config_subscription_t)) };
    arg_kv_t        arg;
    while ((arg = arg_kv_next(argc, argv)).key_hash != 0) {
        assert(arg.value != NULL);
        if ((arg_kv_hash("sub") == arg.key_hash) || (arg_kv_hash("subord") == arg.key_hash)) {
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
    (void)fprintf(stderr, "subscriptions:\n");
    for (size_t i = 0; i < cfg.sub_count; i++) {
        (void)fprintf(stderr, "\t%s\n", cfg.subs[i].name);
    }
    (void)fprintf(stderr, "---\n");
    return cfg;
}

static void on_message(cy_future_t* const subscriber)
{
    if (!cy_future_done(subscriber)) { // Message not available yet, this is an error update.
        char subscriber_name[CY_TOPIC_NAME_MAX];
        cy_subscriber_name(subscriber, subscriber_name);
        (void)fprintf(stderr, "➡️ '%s' request error: %d...\n", subscriber_name, cy_future_error(subscriber));
        return;
    }
    const cy_arrival_t arrival = cy_arrival_move(subscriber);

    // Liveness monitoring is an optional feature that is enabled via cy_subscriber_timeout_set().
    // If disabled, the future may only be done when a new message is pending.
    if (arrival.message.content == NULL) {
        char subscriber_name[CY_TOPIC_NAME_MAX];
        cy_subscriber_name(subscriber, subscriber_name);
        (void)fprintf(stderr,
                      "➡️ '%s' liveness timeout: no messages in %.3f seconds\n",
                      subscriber_name,
                      1e-6 * (double)cy_subscriber_timeout(subscriber));
        return;
    }

    const size_t  payload_size = cy_message_size(arrival.message.content);
    unsigned char payload_copy[(payload_size > 0U) ? payload_size : 1U];
    const void*   payload = NULL;
    if (payload_size > 0U) {
        (void)cy_message_read(arrival.message.content, 0, payload_size, payload_copy);
        payload = payload_copy;
    }
    char* const                 dump  = hexdump(payload_size, payload, 32);
    const cy_topic_t* const     topic = cy_topic_find_by_hash(arrival.breadcrumb.cy, arrival.breadcrumb.topic_hash);
    const cy_substitution_set_t substitutions = cy_subscriber_substitutions(subscriber, topic);
    const char* const           topic_name    = (topic != NULL) ? cy_topic_name(topic).str : "<unknown>";
    (void)fprintf(stderr,
                  "💬 ts=%.6f sz=%06zu sbt=%zu topic='%s'\n%s\n",
                  1e-6 * (double)arrival.message.timestamp,
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
            (void)fprintf(stderr, "cy_respond: %d\n", err);
        }
    } else {
        (void)fprintf(stderr, "not responding, the remote will time out\n");
    }
    cy_message_refcount_dec(arrival.message.content);
}

int main(int argc, char* argv[])
{
    srand((unsigned)time(NULL));
    const example_platform_t platform = example_platform_make(&argc, argv);
    if (platform.platform == NULL) {
        return 1;
    }
    const struct config_t cfg = load_config(argc, argv);

    // Set up the node instance.
    cy_t* const cy = cy_new(platform.platform, example_platform_home(), example_platform_namespace());
    if (cy == NULL) {
        (void)fprintf(stderr, "cy_new\n");
        free(cfg.subs);
        return 1;
    }

    // Create subscribers.
    cy_future_t* subscribers[cfg.sub_count];
    for (size_t i = 0; i < cfg.sub_count; i++) {
        subscribers[i] = cfg.subs[i].ordered ? cy_subscribe_ordered(cy, cy_str(cfg.subs[i].name), MEGA, MEGA)
                                             : cy_subscribe(cy, cy_str(cfg.subs[i].name), MEGA);
        if (subscribers[i] == NULL) {
            (void)fprintf(stderr, "cy_subscribe(): NULL\n");
            free(cfg.subs);
            return 1;
        }
        cy_future_callback_set(subscribers[i], on_message);
    }

    // Spin the event loop.
    while (true) {
        const cy_err_t err_spin = cy_spin_until(cy, cy_now(cy) + MEGA);
        if (err_spin != CY_OK) {
            (void)fprintf(stderr, "cy_spin_until: %d\n", err_spin);
            break;
        }
    }
    free(cfg.subs);
    return 0;
}
