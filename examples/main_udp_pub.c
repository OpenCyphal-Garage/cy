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

struct config_publication_t
{
    const char* name;
};

struct config_t
{
    uint64_t local_uid;
    uint32_t iface_address[CY_UDP_POSIX_IFACE_COUNT_MAX];
    size_t   tx_queue_capacity;

    size_t                       pub_count;
    struct config_publication_t* pubs;
};

static struct config_t load_config(const int argc, const char* const argv[])
{
    struct config_t cfg = {
        .local_uid         = eui64_semirandom(),
        .tx_queue_capacity = 1000,
        .pub_count         = 0,
        .pubs              = calloc((size_t)(argc - 1), sizeof(struct config_publication_t)),
    };
    size_t   iface_count = 0;
    arg_kv_t arg;
    while ((arg = arg_kv_next(argc, argv)).key_hash != 0) {
        assert(arg.value != NULL);
        if ((arg_kv_hash("iface") == arg.key_hash) && (iface_count < CY_UDP_POSIX_IFACE_COUNT_MAX)) {
            cfg.iface_address[iface_count++] = cy_udp_parse_iface_address(arg.value);
        } else if (arg_kv_hash("txq") == arg.key_hash) {
            cfg.tx_queue_capacity = strtoul(arg.value, NULL, 0);
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
        (void)fprintf(stderr, " 0x%08jx", (uintmax_t)cfg.iface_address[i]);
    }
    (void)fprintf(stderr, "\nuid: 0x%016jx\n", (uintmax_t)cfg.local_uid);
    (void)fprintf(stderr, "tx_queue_frames: %zu\n", cfg.tx_queue_capacity);
    (void)fprintf(stderr, "publications:\n");
    for (size_t i = 0; i < cfg.pub_count; i++) {
        (void)fprintf(stderr, "\t%s\n", cfg.pubs[i].name);
    }
    (void)fprintf(stderr, "---\n");
    return cfg;
}

static void on_result(cy_future_t* const future)
{
    const cy_topic_t* const topic = cy_future_context(future).ptr[0];
    const cy_str_t          topic_name =
      (topic != NULL) ? cy_topic_name(topic) : cy_str("<unknown>"); // Topic names are NUL-terminated.
    if (!cy_future_done(future)) { // Future not complete yet, this is an intermediate progress update.
        (void)fprintf(stderr, "➡️ '%s' request delivered; waiting for response...\n", topic_name.str);
        return;
    }

    const cy_err_t err = cy_future_error(future);
    if (err == CY_OK) {
        const cy_response_t response = cy_response_move(future);
        if (response.message.content == NULL) {
            (void)fprintf(stderr, "⌛ topic='%s' response missing despite success state ❌\n", topic_name.str);
            cy_future_destroy(future);
            return;
        }
        const size_t  size = cy_message_size(response.message.content);
        unsigned char data[size];
        cy_message_read(response.message.content, 0, size, data);
        char* const dump = hexdump(size, data, 32); // just a simple visualization aid unrelated to the API
        (void)fprintf(stderr,
                      "↩️ ts=%09ju remote=%016jx seqno=%ju sz=%06zu topic='%s' response ✅\n%s\n",
                      (uintmax_t)response.message.timestamp,
                      (uintmax_t)response.remote_id,
                      (uintmax_t)response.seqno,
                      size,
                      topic_name.str,
                      (dump != NULL) ? dump : "<hexdump failed>");
        free(dump);
        cy_message_refcount_dec(response.message.content);
        cy_future_destroy(future);
    } else {
        (void)fprintf(stderr, "⌛ topic='%s' response failed err=%jd ❌\n", topic_name.str, (intmax_t)err);
        cy_future_destroy(future);
    }
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

    // Create publishers.
    cy_publisher_t* publishers[cfg.pub_count];
    for (size_t i = 0; i < cfg.pub_count; i++) {
        publishers[i] = cy_advertise_client(cy, cy_str(cfg.pubs[i].name), MEGA);
        if (publishers[i] == NULL) {
            (void)fprintf(stderr, "cy_advertise_client: NULL\n");
            return 1;
        }
    }

    // Spin the event loop and publish messages on the topics.
    cy_us_t next_publish_at = cy_now(cy) + MEGA;
    while (true) {
        const cy_err_t err_spin = cy_spin_until(cy, next_publish_at);
        if (err_spin != CY_OK) {
            (void)fprintf(stderr, "cy_udp_posix_spin_once: %jd\n", (intmax_t)err_spin);
            break;
        }
        // Publish messages. This only involves the abstract Cy API.
        const cy_us_t now = cy_now(cy);
        if (now >= next_publish_at) {
            for (size_t i = 0; i < cfg.pub_count; i++) {
                char msg[256];
                (void)sprintf(
                  msg, "Hello from %016jx! The current time is %jd us.", (uintmax_t)cfg.local_uid, (intmax_t)now);
                cy_future_t* const future = cy_request(publishers[i], //
                                                       now + (MEGA * 2),
                                                       MEGA * 10,
                                                       (cy_bytes_t){ .size = strlen(msg), .data = msg });
                if (future == NULL) {
                    (void)fprintf(stderr, "cy_request\n");
                    break;
                }
                cy_future_context_set(future, (cy_user_context_t){ { (void*)cy_publisher_topic(publishers[i]) } });
                cy_future_callback_set(future, on_result);
            }
            next_publish_at += 5 * MEGA;
        }
    }
    return 0;
}
