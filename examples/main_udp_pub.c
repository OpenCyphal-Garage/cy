#include "cy_udp_posix.h"
#include "util.h"
#include "arg_kv.h"
#include "hexdump.h"
#include <time.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

// ReSharper disable CppDFAMemoryLeak

struct config_publication_t
{
    const char* name;
};

struct config_t
{
    uint64_t local_uid;
    uint32_t iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX];
    size_t   tx_queue_capacity;

    const char* namespace;

    size_t                       pub_count;
    struct config_publication_t* pubs;
};

static struct config_t load_config(const int argc, char* argv[])
{
    struct config_t cfg = {
        .local_uid         = volatile_eui64(),
        .tx_queue_capacity = 1000,
        .namespace         = NULL, // will use the default namespace by default.
        .pub_count         = 0,
        .pubs              = calloc((size_t)(argc - 1), sizeof(struct config_publication_t)),
    };
    size_t   iface_count = 0;
    arg_kv_t arg;
    while ((arg = arg_kv_next(argc, argv)).key_hash != 0) {
        assert(arg.value != NULL);
        if ((arg_kv_hash("iface") == arg.key_hash) && (iface_count < CY_UDP_POSIX_IFACE_COUNT_MAX)) {
            cfg.iface_address[iface_count++] = udp_wrapper_parse_iface_address(arg.value);
        } else if (arg_kv_hash("txq") == arg.key_hash) {
            cfg.tx_queue_capacity = strtoul(arg.value, NULL, 0);
        } else if (arg_kv_hash("ns") == arg.key_hash) {
            cfg.namespace = arg.value;
        } else if (arg_kv_hash("pub") == arg.key_hash) {
            struct config_publication_t* x = NULL;
            for (size_t i = 0; i < cfg.pub_count; i++) {
                if (strcmp(cfg.pubs[i].name, arg.value) == 0) {
                    x = &cfg.pubs[i];
                }
            }
            x       = (x == NULL) ? &cfg.pubs[cfg.pub_count++] : x;
            x->name = arg.value;
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
    (void)fprintf(stderr, "publications:\n");
    for (size_t i = 0; i < cfg.pub_count; i++) {
        (void)fprintf(stderr, "\t%s\n", cfg.pubs[i].name);
    }
    (void)fprintf(stderr, "---\n");
    return cfg;
}

static void on_message_delivery_result(const cy_user_context_t user, const uint16_t acks)
{
    cy_topic_t* const topic = user.ptr[1];
    CY_TRACE(topic->cy, "'%s' %s %u acks", topic->name, (acks > 0) ? "✅" : "❌", (unsigned)acks);
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_response(const cy_user_context_t user, cy_message_ts_t* const msg)
{
    cy_topic_t* const topic = user.ptr[1];
    assert(topic != NULL);
    if (msg == NULL) {
        CY_TRACE(topic->cy, "↩️⌛ sid=%04x topic='%s' response timed out", cy_topic_subject_id(topic), topic->name);
        return;
    }
    const size_t  payload_size = cy_message_size(msg->content);
    unsigned char payload_copy[payload_size];
    cy_message_read(&msg->content, 0, payload_size, payload_copy);
    char* const dump = hexdump(payload_size, payload_copy, 32);
    CY_TRACE(topic->cy,
             "↩️ ts=%09llu sid=%04x sz=%06zu topic='%s'\n%s",
             (unsigned long long)msg->timestamp,
             cy_topic_subject_id(topic),
             payload_size,
             topic->name,
             dump);
    free(dump);
}

int main(const int argc, char* argv[])
{
    srand((unsigned)time(NULL));
    const struct config_t cfg = load_config(argc, argv);

    // Set up the node instance.
    cy_udp_posix_t cy_udp_posix;
    const cy_err_t res = cy_udp_posix_new(&cy_udp_posix, //
                                          cfg.local_uid,
                                          wkv_key(NULL),
                                          wkv_key(cfg.namespace),
                                          cfg.iface_address,
                                          cfg.tx_queue_capacity);
    if (res != CY_OK) {
        (void)fprintf(stderr, "cy_udp_posix_new: %d\n", res);
        return 1;
    }
    cy_t* const cy             = &cy_udp_posix.base;
    cy->implicit_topic_timeout = 10 * MEGA; // This is just for debugging purposes.

    // Create publishers.
    cy_publisher_t* publishers[cfg.pub_count];
    for (size_t i = 0; i < cfg.pub_count; i++) {
        publishers[i] = cy_advertise_client(cy, wkv_key(cfg.pubs[i].name), MEGA);
        if (publishers[i] == NULL) {
            (void)fprintf(stderr, "cy_advertise_client: NULL\n");
            return 1;
        }
    }

    // Spin the event loop and publish messages on the topics.
    cy_us_t next_publish_at = cy_now(cy) + MEGA;
    while (true) {
        // The event loop spin API is platform-specific, too.
        const cy_err_t err_spin = cy_udp_posix_spin_once(&cy_udp_posix);
        if (err_spin != CY_OK) {
            (void)fprintf(stderr, "cy_udp_posix_spin_once: %d\n", err_spin);
            break;
        }
        // Publish messages. This only involves the abstract Cy API.
        const cy_us_t now = cy_now(cy);
        if (now >= next_publish_at) {
            for (size_t i = 0; i < cfg.pub_count; i++) {
                char msg[256];
                (void)sprintf(msg,
                              "Hello from %016llx! The current time is %lld us.",
                              (unsigned long long)cfg.local_uid,
                              (long long)now);
                const cy_user_context_t ctx = {
                    .ptr = { NULL, (void*)cy_publisher_topic(publishers[i]), NULL, NULL },
                };
                const cy_err_t pub_res = cy_request(publishers[i],
                                                    now + (MEGA * 2),
                                                    now + (MEGA * 10),
                                                    (cy_bytes_t){ .size = strlen(msg), .data = msg },
                                                    ctx,
                                                    on_message_delivery_result,
                                                    ctx,
                                                    on_response);
                if (pub_res != CY_OK) {
                    (void)fprintf(stderr, "cy_request: %d\n", pub_res);
                    break;
                }
            }
            next_publish_at += 5 * MEGA;
        }
    }
    return 0;
}
