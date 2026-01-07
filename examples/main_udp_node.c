#include "util.h"
#include "cy_udp_posix.h"
#include <time.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>

// ReSharper disable CppDFAMemoryLeak
// NOLINTBEGIN(*-err33-c,*-core.NonNullParamChecker)

#define KILO 1000L
#define MEGA (KILO * 1LL * KILO)

static uint64_t arg_kv_hash(const char* s) { return rapidhash(s, strlen(s)); }

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
    size_t   tx_queue_capacity;

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
        .local_uid         = volatile_eui64(),
        .tx_queue_capacity = 1000,
        .namespace         = NULL, // will use the default namespace by default.
        .pub_count         = 0,
        .pubs              = calloc((size_t)(argc - 1), sizeof(struct config_publication_t)),
        .sub_count         = 0,
        .subs              = calloc((size_t)(argc - 1), sizeof(struct config_subscription_t)),
    };

    // Parse CLI args.
    size_t          iface_count = 0;
    struct arg_kv_t arg;
    while ((arg = arg_kv_next(argc, argv)).key_hash != 0) {
        if ((arg_kv_hash("iface") == arg.key_hash) && (iface_count < CY_UDP_POSIX_IFACE_COUNT_MAX)) {
            cfg.iface_address[iface_count++] = udp_wrapper_parse_iface_address(arg.value);
        } else if (arg_kv_hash("uid") == arg.key_hash) {
            cfg.local_uid = strtoull(arg.value, NULL, 0);
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
    fprintf(stderr, "tx queue %zu frames\n", cfg.tx_queue_capacity);
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

static void on_delivery_result_message(const cy_user_context_t user, const uint16_t acknowledgements)
{
    bool* const done_flag = (bool*)user.ptr[0];
    assert((done_flag != NULL) && !*done_flag);
    *done_flag              = true;
    cy_topic_t* const topic = user.ptr[1];
    printf("Message delivery on '%s': %s %u acks\n",
           topic->name,
           (acknowledgements > 0) ? "✅" : "❌",
           (unsigned)acknowledgements);
}

static void on_delivery_result_response(const cy_user_context_t user, const uint16_t acknowledgements)
{
    bool* const done_flag = (bool*)user.ptr[0];
    assert((done_flag != NULL) && !*done_flag);
    *done_flag = true;
    assert(acknowledgements <= 1);
    cy_topic_t* const topic = user.ptr[1];
    printf("Response delivery on '%s': %s\n", topic->name, (acknowledgements == 1) ? "✅" : "❌");
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_msg_trace(cy_user_context_t user, cy_arrival_t* const arrival)
{
    const size_t  payload_size = cy_message_size(arrival->message.content);
    unsigned char payload_copy[payload_size];
    cy_message_read(&arrival->message.content, 0, payload_size, payload_copy);

    // Convert payload to hex.
    char hex[(payload_size * 2) + 1];
    for (size_t i = 0; i < payload_size; i++) {
        sprintf(hex + (i * 2), "%02x", ((const unsigned char*)payload_copy)[i]);
    }
    hex[sizeof(hex) - 1] = '\0';

    // Convert payload to ASCII.
    char ascii[payload_size + 1];
    for (size_t i = 0; i < payload_size; i++) {
        const char ch = ((const char*)payload_copy)[i];
        ascii[i]      = isprint(ch) ? ch : '.';
    }
    ascii[payload_size] = '\0';

    // Log the message.
    CY_TRACE(arrival->topic->cy,
             "💬 ts=%09llu sid=%04x sz=%06zu sbt=%zu topic='%s'\n%s\n%s",
             (unsigned long long)arrival->message.timestamp,
             cy_topic_subject_id(arrival->topic),
             payload_size,
             arrival->substitutions.count,
             cy_topic_name(arrival->topic).str,
             hex,
             ascii);

    // Optionally, send a direct p2p response to the publisher of this message.
    if ((rand() % 2) == 0) {
        *(bool*)user.ptr[0] = false; // reset the flag for the response delivery
        user.ptr[1]         = (void*)arrival->topic;
        const cy_err_t err  = cy_respond(arrival->responder,
                                        arrival->message.timestamp + MEGA,
                                        (cy_bytes_t){ .size = 2, .data = ":3" },
                                        user,
                                        on_delivery_result_response);
        if (err != CY_OK) {
            fprintf(stderr, "cy_respond: %d\n", err);
        }
    }
}

// ReSharper disable once CppParameterMayBeConstPtrOrRef
static void on_response_trace(const cy_user_context_t user, cy_message_ts_t* const msg)
{
    cy_topic_t* const topic = user.ptr[1];
    assert(topic != NULL);
    if (msg != NULL) {
        const size_t  payload_size = cy_message_size(msg->content);
        unsigned char payload_copy[payload_size];
        cy_message_read(&msg->content, 0, payload_size, payload_copy);

        // Convert payload to hex.
        char hex[(payload_size * 2) + 1];
        for (size_t i = 0; i < payload_size; i++) {
            sprintf(hex + (i * 2), "%02x", ((const uint8_t*)payload_copy)[i]);
        }
        hex[sizeof(hex) - 1] = '\0';

        // Convert payload to ASCII.
        char ascii[payload_size + 1];
        for (size_t i = 0; i < payload_size; i++) {
            const char ch = ((const char*)payload_copy)[i];
            ascii[i]      = isprint(ch) ? ch : '.';
        }
        ascii[payload_size] = '\0';

        // Log the response.
        CY_TRACE(topic->cy,
                 "↩️ ts=%09llu sid=%04x sz=%06zu topic='%s'\n%s\n%s",
                 (unsigned long long)msg->timestamp,
                 cy_topic_subject_id(topic),
                 payload_size,
                 topic->name,
                 hex,
                 ascii);
    } else {
        CY_TRACE(topic->cy, "↩️⌛ sid=%04x topic='%s' response timed out", cy_topic_subject_id(topic), topic->name);
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
        const cy_err_t res = cy_udp_posix_new(&cy_udp_posix, //
                                              cfg.local_uid,
                                              wkv_key(NULL),
                                              wkv_key(cfg.namespace),
                                              cfg.iface_address,
                                              cfg.tx_queue_capacity);
        if (res != CY_OK) {
            fprintf(stderr, "cy_udp_posix_new: %d\n", res);
            return 1;
        }
    }
    cy_t* const cy = &cy_udp_posix.base;

    // This is just for debugging purposes.
    cy->implicit_topic_timeout = 10 * MEGA;

    // ------------------------------  End of the platform- and transport-specific part  ------------------------------

    // Create publishers.
    cy_publisher_t* publishers[cfg.pub_count];
    bool            message_delivery_flags[cfg.pub_count];
    for (size_t i = 0; i < cfg.pub_count; i++) {
        publishers[i] = cy_advertise_client(cy, wkv_key(cfg.pubs[i].name), MEGA);
        if (publishers[i] == NULL) {
            fprintf(stderr, "cy_advertise_client: NULL\n");
            return 1;
        }
        message_delivery_flags[i] = true;
    }

    // Create subscribers.
    cy_subscriber_t* subscribers[cfg.sub_count];
    bool             response_delivery_flags[cfg.sub_count];
    for (size_t i = 0; i < cfg.sub_count; i++) {
        subscribers[i] = cy_subscribe(cy,
                                      wkv_key(cfg.subs[i].name),
                                      MEGA,
                                      (cy_user_context_t){ .ptr = { &response_delivery_flags[i] } },
                                      on_msg_trace);
        if (subscribers[i] == NULL) {
            fprintf(stderr, "cy_subscribe: NULL\n");
            return 1;
        }
        response_delivery_flags[i] = false;
    }

    // Spin the event loop and publish messages on the topics.
    cy_us_t next_publish_at = cy_now(cy) + MEGA;
    while (true) {
        // The event loop spin API is platform-specific, too.
        const cy_err_t err_spin = cy_udp_posix_spin_once(&cy_udp_posix);
        if (err_spin != CY_OK) {
            fprintf(stderr, "cy_udp_posix_spin_once: %d\n", err_spin);
            break;
        }
        // Publish messages.
        // It would be nice to have olga_scheduler ported to C11... See https://github.com/Zubax/olga_scheduler
        const cy_us_t now = cy_now(cy);
        if (now >= next_publish_at) {
            for (size_t i = 0; i < cfg.pub_count; i++) {
                if (!message_delivery_flags[i]) {
                    continue; // still pending
                }
                char msg[256];
                sprintf(msg,
                        "Hello from %016llx! The current time is %lld us.",
                        (unsigned long long)cfg.local_uid,
                        (long long)now);
                const cy_user_context_t ctx = {
                    .ptr = { &message_delivery_flags[i], (void*)cy_publisher_topic(publishers[i]) },
                };
                const cy_err_t pub_res = cy_request(publishers[i],
                                                    now + (KILO * 100),
                                                    now + (MEGA * 60),
                                                    (cy_bytes_t){ .size = strlen(msg), .data = msg },
                                                    ctx,
                                                    on_delivery_result_message,
                                                    ctx,
                                                    on_response_trace);
                if (pub_res != CY_OK) {
                    fprintf(stderr, "cy_publish: %d\n", pub_res);
                    break;
                }
            }
            next_publish_at += 5000000U;
        }
    }

    return 0;
}

// NOLINTEND(*-err33-c,*-core.NonNullParamChecker)
