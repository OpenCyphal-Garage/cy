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

struct config_publication_t
{
    const char* name;
};

struct config_t
{
    size_t                       pub_count;
    struct config_publication_t* pubs;
};

static struct config_t load_config(const int argc, char* const argv[])
{
    const size_t    config_capacity = (size_t)((argc > 1) ? (argc - 1) : 1);
    struct config_t cfg = { .pub_count = 0, .pubs = calloc(config_capacity, sizeof(struct config_publication_t)) };
    arg_kv_t        arg;
    while ((arg = arg_kv_next(argc, argv)).key_hash != 0) {
        assert(arg.value != NULL);
        if (arg_kv_hash("pub") == arg.key_hash) {
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
    const cy_err_t err = cy_future_error(future);
    if (!cy_future_done(future)) { // Future not complete yet, this is an intermediate update.
        (void)fprintf(stderr, "➡️ '%s' request error: %d...\n", topic_name.str, err);
        return;
    }
    if (err == CY_OK) {
        const cy_response_t response = cy_response_move(future);
        assert(response.message.content != NULL); // guaranteed because we're done and OK.
        const size_t  size = cy_message_size(response.message.content);
        unsigned char data[(size > 0U) ? size : 1U];
        const void*   payload = NULL;
        if (size > 0U) {
            (void)cy_message_read(response.message.content, 0, size, data);
            payload = data;
        }
        char* const dump = hexdump(size, payload, 32); // just a simple visualization aid unrelated to the API
        (void)fprintf(stderr,
                      "↩️ ts=%.6f remote=%016llx seqno=%llu sz=%06zu topic='%s' response ✅\n%s\n",
                      1e-6 * (double)response.message.timestamp,
                      (unsigned long long)response.remote_id,
                      (unsigned long long)response.seqno,
                      size,
                      topic_name.str,
                      (dump != NULL) ? dump : "<hexdump failed>");
        free(dump);
        cy_message_refcount_dec(response.message.content); // release the message when no longer needed
    } else {
        (void)fprintf(stderr, "⌛ topic='%s' response failed err=%d ❌\n", topic_name.str, err);
    }
    cy_future_destroy(future);
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
            (void)fprintf(stderr, "cy_udp_posix_spin_once: %d\n", err_spin);
            break;
        }
        // Publish messages.
        const cy_us_t now = cy_now(cy);
        if (now >= next_publish_at) {
            for (size_t i = 0; i < cfg.pub_count; i++) {
                char msg[256];
                (void)sprintf(msg, "Hello from %s! The current time is %.6f s.", cy_home(cy).str, 1e-6 * (double)now);
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
