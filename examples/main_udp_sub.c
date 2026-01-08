#include "cy_udp_posix.h"
#include "eui64.h"
#include "arg_kv.h"
#include "hexdump.h"
#include <time.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

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

static struct config_t load_config(const int argc, char* argv[])
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
            cfg.iface_address[iface_count++] = udp_wrapper_parse_iface_address(arg.value);
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
        (void)fprintf(stderr, " 0x%08x", cfg.iface_address[i]);
    }
    (void)fprintf(stderr, "\nuid: 0x%016llx\n", (unsigned long long)cfg.local_uid);
    (void)fprintf(stderr, "tx_queue_frames: %zu\n", cfg.tx_queue_capacity);
    (void)fprintf(stderr, "subscriptions:\n");
    for (size_t i = 0; i < cfg.sub_count; i++) {
        (void)fprintf(stderr, "\t%s\n", cfg.subs[i].name);
    }
    (void)fprintf(stderr, "---\n");
    return cfg;
}

static void on_response_delivery_result(const cy_user_context_t user, const uint16_t acknowledgements)
{
    bool* const done_flag = (bool*)user.ptr[0];
    assert((done_flag != NULL) && !*done_flag);
    *done_flag = true;
    assert(acknowledgements <= 1);
    const cy_topic_t* const topic = user.ptr[1];
    CY_TRACE(topic->cy, "'%s' %s", topic->name, (acknowledgements == 1) ? "✅" : "❌");
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_message(cy_user_context_t user, cy_arrival_t* const arrival)
{
    const size_t  payload_size = cy_message_size(arrival->message.content);
    unsigned char payload_copy[payload_size];
    cy_message_read(&arrival->message.content, 0, payload_size, payload_copy);
    char* const dump = hexdump(payload_size, payload_copy, 32);
    CY_TRACE(arrival->topic->cy,
             "💬 ts=%09llu sid=%04x sz=%06zu sbt=%zu topic='%s'\n%s",
             (unsigned long long)arrival->message.timestamp,
             cy_topic_subject_id(arrival->topic),
             payload_size,
             arrival->substitutions.count,
             cy_topic_name(arrival->topic).str,
             dump);
    // Optionally, send a response to the publisher of this message.
    // The stack knows the identity of the publisher and can deliver a response directly to it.
    if ((rand() % 2) == 0) {
        *(bool*)user.ptr[0] = false; // reset the flag for the response delivery
        user.ptr[1]         = (void*)arrival->topic;
        const cy_err_t err  = cy_respond(arrival->responder,
                                        arrival->message.timestamp + MEGA,
                                        (cy_bytes_t){ .size = 2, .data = ":3" },
                                        user,
                                        on_response_delivery_result);
        if (err != CY_OK) {
            (void)fprintf(stderr, "cy_respond: %d\n", err);
        }
    }
}

int main(const int argc, char* argv[])
{
    srand((unsigned)time(NULL));
    const struct config_t cfg = load_config(argc, argv);

    // Set up the node instance.
    cy_udp_posix_t cy_udp_posix;
    const cy_err_t res = cy_udp_posix_new(&cy_udp_posix, //
                                          cfg.local_uid,
                                          wkv_key(""),
                                          wkv_key(""),
                                          cfg.iface_address,
                                          cfg.tx_queue_capacity);
    if (res != CY_OK) {
        (void)fprintf(stderr, "cy_udp_posix_new: %d\n", res);
        return 1;
    }
    cy_t* const cy             = &cy_udp_posix.base;
    cy->implicit_topic_timeout = 10 * MEGA; // This is just for debugging purposes.

    // Create subscribers.
    cy_subscriber_t* subscribers[cfg.sub_count];
    bool             response_delivery_flags[cfg.sub_count];
    for (size_t i = 0; i < cfg.sub_count; i++) {
        subscribers[i] = cy_subscribe(cy,
                                      wkv_key(cfg.subs[i].name),
                                      MEGA,
                                      (cy_user_context_t){ .ptr = { &response_delivery_flags[i] } },
                                      on_message);
        if (subscribers[i] == NULL) {
            (void)fprintf(stderr, "cy_subscribe: NULL\n");
            return 1;
        }
        response_delivery_flags[i] = false;
    }

    // Spin the event loop.
    while (true) {
        const cy_err_t err_spin = cy_udp_posix_spin_once(&cy_udp_posix);
        if (err_spin != CY_OK) {
            (void)fprintf(stderr, "cy_udp_posix_spin_once: %d\n", err_spin);
            break;
        }
    }
    return 0;
}
