#include "cy_udp_posix.h"
#include <rapidhash.h>
#include <time.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <ctype.h>

static uint64_t random_uid(void)
{
    const uint16_t vid = UINT16_MAX; // This is the reserved public VID.
    const uint16_t pid = (uint16_t)rand();
    const uint32_t iid = (uint32_t)rand();
    return (((uint64_t)vid) << 48U) | (((uint64_t)pid) << 32U) | iid;
}

static uint64_t arg_kv_hash(const char* s)
{
    return rapidhash(s, strlen(s));
}

/// The pointed strings have a static lifetime.
struct arg_kv_t
{
    size_t      index;    ///< Argument index, where 0 is the program name.
    const char* key;      ///< NULL key indicates that no more arguments are available.
    uint64_t    key_hash; ///< arg_kv_hash(key); 0 if no key.
    const char* value;    ///< NULL unless the argument matches "key=value". May be empty if "key=".
};

/// Returns the next argument key/value pair at every invocation. Returns NULL key when there are no more arguments.
/// Invokes exit(1) with a message if the arguments are malformed.
/// The argv array past the zeroth index may be mutated.
static struct arg_kv_t arg_kv_next(const int argc, char* argv[])
{
    if (argc <= 1) {
        fprintf(stderr,
                "Usage:\n\t%s key1[=value1] [key2[=value2] ...]\n"
                "No spaces around '=' are allowed.",
                argv[0]);
        exit(1);
    }
    static size_t   index = 1;
    struct arg_kv_t out   = { .index = index++, .key = NULL, .key_hash = 0, .value = NULL };
    if (((int)out.index) < argc) {
        out.key       = argv[out.index];
        char* const q = strchr(out.key, '=');
        if (q != NULL) {
            *q        = '\0';
            out.value = q + 1;
        }
        out.key_hash = arg_kv_hash(out.key);
    }
    return out;
}

struct config_publication_t
{
    const char* name;
};

struct config_subscription_t
{
    const char* name;
};

struct config_t
{
    uint32_t iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX];
    uint64_t local_uid;
    size_t   tx_queue_capacity_per_iface;

    const char* namespace;

    size_t                       pub_count;
    struct config_publication_t* pubs;

    size_t                        sub_count;
    struct config_subscription_t* subs;
};

static struct config_t load_config(const int argc, char* argv[])
{
    // Load default config.
    struct config_t cfg = {
        .local_uid                   = random_uid(),
        .tx_queue_capacity_per_iface = 1000,
        .namespace                   = NULL, // will use the default namespace by default.
        .pub_count                   = 0,
        .pubs                        = calloc((size_t)(argc - 1), sizeof(struct config_publication_t)),
        .sub_count                   = 0,
        .subs                        = calloc((size_t)(argc - 1), sizeof(struct config_subscription_t)),
    };

    // Parse CLI args.
    size_t          iface_count = 0;
    struct arg_kv_t arg;
    while ((arg = arg_kv_next(argc, argv)).key_hash != 0) {
        if ((arg_kv_hash("iface") == arg.key_hash) && (iface_count < CY_UDP_POSIX_IFACE_COUNT_MAX)) {
            cfg.iface_address[iface_count++] = udp_wrapper_parse_iface_address(arg.value);
        } else if (arg_kv_hash("uid") == arg.key_hash) {
            cfg.local_uid = strtoull(arg.value, NULL, 0);
        } else if (arg_kv_hash("tx_queue_capacity") == arg.key_hash) {
            cfg.tx_queue_capacity_per_iface = strtoul(arg.value, NULL, 0);
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
        } else if (arg_kv_hash("sub") == arg.key_hash) {
            struct config_subscription_t* x = NULL;
            for (size_t i = 0; i < cfg.sub_count; i++) {
                if (strcmp(cfg.subs[i].name, arg.value) == 0) {
                    x = &cfg.subs[i];
                }
            }
            x       = (x == NULL) ? &cfg.subs[cfg.sub_count++] : x;
            x->name = arg.value;
        } else {
            fprintf(stderr, "Unexpected key #%zu: '%s'\n", arg.index, arg.key);
            exit(1);
        }
    }

    // Print the actual configs we're using.
    fprintf(stderr, "ifaces:");
    for (size_t i = 0; i < CY_UDP_POSIX_IFACE_COUNT_MAX; i++) {
        fprintf(stderr, " 0x%08x", cfg.iface_address[i]);
    }
    fprintf(stderr, "\nuid: 0x%016llx\n", (unsigned long long)cfg.local_uid);
    fprintf(stderr, "tx_queue_capacity: %zu\n", cfg.tx_queue_capacity_per_iface);
    fprintf(stderr, "publications:\n");
    for (size_t i = 0; i < cfg.pub_count; i++) {
        fprintf(stderr, "\t%s\n", cfg.pubs[i].name);
    }
    fprintf(stderr, "subscriptions:\n");
    for (size_t i = 0; i < cfg.sub_count; i++) {
        fprintf(stderr, "\t%s\n", cfg.subs[i].name);
    }
    fprintf(stderr, "---\n");
    return cfg;
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_msg_trace(cy_t* const cy, const cy_arrival_t* const arv)
{
    CY_BUFFER_GATHER_ON_STACK(payload, arv->transfer->payload.base)

    // Convert linearized payload to hex.
    char hex[payload.size * 2 + 1];
    for (size_t i = 0; i < payload.size; i++) {
        sprintf(hex + i * 2, "%02x", ((const uint8_t*)payload.data)[i]);
    }
    hex[sizeof(hex) - 1] = '\0';

    // Convert linearized payload to ASCII.
    char ascii[payload.size + 1];
    for (size_t i = 0; i < payload.size; i++) {
        const char ch = ((const char*)payload.data)[i];
        ascii[i]      = isprint(ch) ? ch : '.';
    }
    ascii[payload.size] = '\0';

    // Log the message.
    CY_TRACE(cy,
             "💬 [sid=%04x nid=%04x tid=%016llx sz=%06zu ts=%09llu] @ '%s' [age=%llu]:\n%s\n%s",
             cy_topic_subject_id(arv->topic),
             arv->transfer->metadata.remote_node_id,
             (unsigned long long)arv->transfer->metadata.transfer_id,
             payload.size,
             (unsigned long long)arv->transfer->timestamp,
             cy_topic_name(arv->topic).str,
             (unsigned long long)arv->topic->age,
             hex,
             ascii);
    // TODO: log substitutions.

    // Optionally, send a direct p2p response to the publisher of this message.
    if (cy_joined(cy) && ((rand() % 2) == 0)) {
        const cy_err_t err = cy_respond(cy,
                                        arv->topic, //
                                        arv->transfer->timestamp + 1000000,
                                        arv->transfer->metadata,
                                        (cy_buffer_borrowed_t){ .view = { .data = ":3", .size = 2 } });
        if (err != CY_OK) {
            fprintf(stderr, "cy_respond: %d\n", err);
        }
    }
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_response_trace(cy_t* const cy, cy_future_t* const future)
{
    cy_topic_t* topic = future->publisher->topic;
    if (future->state == cy_future_success) {
        cy_transfer_owned_t* const transfer = &future->last_response;
        CY_BUFFER_GATHER_ON_STACK(payload, transfer->payload.base)

        // Convert payload to hex.
        char hex[payload.size * 2 + 1];
        for (size_t i = 0; i < payload.size; i++) {
            sprintf(hex + i * 2, "%02x", ((const uint8_t*)payload.data)[i]);
        }
        hex[sizeof(hex) - 1] = '\0';

        // Convert payload to ASCII.
        char ascii[payload.size + 1];
        for (size_t i = 0; i < payload.size; i++) {
            const char ch = ((const char*)payload.data)[i];
            ascii[i]      = isprint(ch) ? ch : '.';
        }
        ascii[payload.size] = '\0';

        // Release the payload buffer memory.
        // This memory comes all the way from the bottom layer of the stack with zero copying.
        // If we don't release it now, it will be released only when the next response arrives, which is wasteful.
        cy_buffer_owned_release(cy, &transfer->payload);

        // Log the response.
        CY_TRACE(cy,
                 "↩️ [sid=%04x nid=%04x tid=%016llx sz=%06zu ts=%09llu] @ %s [age=%llu]:\n%s\n%s",
                 cy_topic_subject_id(topic),
                 transfer->metadata.remote_node_id,
                 (unsigned long long)transfer->metadata.transfer_id,
                 payload.size,
                 (unsigned long long)transfer->timestamp,
                 topic->name,
                 (unsigned long long)topic->age,
                 hex,
                 ascii);
    } else if (future->state == cy_future_response_timeout) {
        CY_TRACE(cy,
                 "↩️⌛ Request to '%s' tid=%016llx (masked) has timed out",
                 future->publisher->topic->name,
                 (unsigned long long)future->transfer_id_masked);
    } else {
        assert(false);
    }
}

int main(const int argc, char* argv[])
{
    srand((unsigned)time(NULL));
    const struct config_t cfg = load_config(argc, argv);

    // Set up the node instance. The initialization is the only platform-specific part.
    // The rest of the API is platform- and transport-agnostic.
    cy_udp_posix_t cy_udp_posix;
    {
        const cy_err_t res = cy_udp_posix_new_c(&cy_udp_posix, //
                                                cfg.local_uid,
                                                cfg.namespace,
                                                cfg.iface_address,
                                                cfg.tx_queue_capacity_per_iface);
        if (res != CY_OK) {
            fprintf(stderr, "cy_udp_posix_new: %d\n", res);
            return 1;
        }
    }
    cy_t* const cy = &cy_udp_posix.base;

    // This is just for debugging purposes.
    cy->implicit_topic_timeout = 10000000;

    // ------------------------------  End of the platform- and transport-specific part  ------------------------------

    // Create publishers.
    cy_publisher_t publishers[cfg.pub_count];
    cy_future_t    futures[cfg.pub_count];
    for (size_t i = 0; i < cfg.pub_count; i++) {
        cy_err_t res = cy_advertise_c(cy, &publishers[i], cfg.pubs[i].name, 1024 * 1024);
        if (res != CY_OK) {
            fprintf(stderr, "cy_topic_new: %u\n", res);
            return 1;
        }
        cy_future_new(&futures[i], on_response_trace, NULL);
    }

    // Create subscribers.
    cy_subscriber_t subscribers[cfg.sub_count];
    for (size_t i = 0; i < cfg.sub_count; i++) {
        cy_err_t res = cy_subscribe_c(cy, &subscribers[i], cfg.subs[i].name, 1024 * 1024, on_msg_trace);
        if (res != CY_OK) {
            fprintf(stderr, "cy_subscribe: %d\n", res);
            return 1;
        }
    }

    // Spin the event loop and publish the topics.
    cy_us_t next_publish_at = cy_now(cy) + 1000000;
    while (true) {
        // The event loop spin API is platform-specific, too.
        const cy_err_t err_spin = cy_udp_posix_spin_once(&cy_udp_posix);
        if (err_spin != CY_OK) {
            fprintf(stderr, "cy_udp_posix_spin_once: %d\n", err_spin);
            break;
        }

        // Publish messages.
        // I'm thinking that it would be nice to have olga_scheduler ported to C11...
        // See https://github.com/Zubax/olga_scheduler
        const cy_us_t now = cy_now(cy);
        if (now >= next_publish_at) {
            if (cy_joined(cy)) {
                for (size_t i = 0; i < cfg.pub_count; i++) {
                    if (futures[i].state == cy_future_pending) {
                        continue;
                    }
                    char msg[256];
                    sprintf(msg,
                            "Hello from %016llx! The current time is %lld us.",
                            (unsigned long long)cy->uid,
                            (long long)now);
                    const cy_err_t pub_res =
                      cy_publish(cy,
                                 &publishers[i],
                                 now + 100000,
                                 (cy_buffer_borrowed_t){ .view = { .data = msg, .size = strlen(msg) } },
                                 now + 1000000,
                                 &futures[i]);
                    if (pub_res != CY_OK) {
                        fprintf(stderr, "cy_publish: %d\n", pub_res);
                        break;
                    }
                }
            }
            next_publish_at += 5000000U;
        }
    }

    return 0;
}
