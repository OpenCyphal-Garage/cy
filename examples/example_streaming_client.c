// A tiny streaming client demo: send one request and keep receiving responses.

#include <cy.h>

#include "example_platform.h"

#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

#define TOPIC_NAME        "demo/stream"
#define DEFAULT_COUNT     10U
#define DEFAULT_PERIOD_ms 500U
#define RESPONSE_MAX      128U

// Request payload (little-endian, for demo simplicity).
typedef struct
{
    uint32_t count;     // cppcheck-suppress unusedStructMember
    uint32_t period_ms; // cppcheck-suppress unusedStructMember
} stream_request_t;

typedef struct
{
    uint32_t expected;
    uint32_t received;
    bool     done;
} client_state_t;

static void on_stream_response(cy_future_t* const future)
{
    client_state_t* const st = (client_state_t*)cy_future_context(future).ptr[0];
    assert(st != NULL);
    if (!cy_future_done(future)) {
        // Intermediate progress update: request has been delivered, waiting for data stream.
        (void)fprintf(stderr, "request delivered, waiting for data stream...\n");
        return;
    }
    if (cy_future_error(future) != CY_OK) {
        (void)fprintf(stderr, "request timed out\n");
        st->done = true;
        cy_future_destroy(future);
        return;
    }
    cy_response_t response = cy_response_move(future);
    char          text[RESPONSE_MAX];
    const size_t  n = cy_message_read(response.message.content, 0, RESPONSE_MAX - 1U, text);
    text[n]         = '\0';
    (void)fprintf(
      stderr, "response seq=%ju remote=%016jx: %s\n", (uintmax_t)response.seqno, (uintmax_t)response.remote_id, text);
    cy_message_refcount_dec(response.message.content);
    st->received++;
    if (st->received >= st->expected) {
        st->done = true;
        // Once the future is destroyed, no further responses will be accepted.
        cy_future_destroy(future);
    }
}

int main(int argc, char* argv[])
{
    const example_platform_t platform = example_platform_make(&argc, argv);
    if (platform.platform == NULL) {
        return 1;
    }

    // Parse optional args: count [period_ms].
    uint32_t count     = DEFAULT_COUNT;
    uint32_t period_ms = DEFAULT_PERIOD_ms;
    if (argc > 1) {
        count = (uint32_t)strtoul(argv[1], NULL, 0);
    }
    if (argc > 2) {
        period_ms = (uint32_t)strtoul(argv[2], NULL, 0);
    }
    if (count == 0) {
        count = DEFAULT_COUNT;
    }
    if (period_ms == 0) {
        period_ms = DEFAULT_PERIOD_ms;
    }

    // Initialize the node.
    cy_t* const cy = cy_new(platform.platform, example_platform_home(), cy_str(getenv("CYPHAL_NAMESPACE")));
    if (cy == NULL) {
        (void)fprintf(stderr, "cy_new\n");
        return 1;
    }
    // Allow the integrator to override hardcoded topic names from the environment.
    (void)cy_remap_parse(cy, cy_str(getenv("CYPHAL_REMAP")));

    // Create the publisher that will issue the request.
    cy_publisher_t* const pub = cy_advertise_client(cy, cy_str(TOPIC_NAME), RESPONSE_MAX);
    if (pub == NULL) {
        (void)fprintf(stderr, "cy_advertise_client\n");
        return 1;
    }

    // Send a single request that asks the server to stream responses.
    const stream_request_t req = { .count = count, .period_ms = period_ms };
    const cy_us_t          now = cy_now(cy);

    cy_future_t* future = cy_request(pub,            //
                                     now + 10000000, // delivery deadline
                                     20000000,       // response timeout
                                     (cy_bytes_t){ .size = sizeof(req), .data = &req });
    if (future == NULL) {
        (void)fprintf(stderr, "cy_request\n");
        return 1;
    }
    client_state_t state = { .expected = count, .received = 0, .done = false };
    cy_future_context_set(future, (cy_user_context_t){ .ptr = { &state } });
    cy_future_callback_set(future, &on_stream_response);
    (void)fprintf(stderr, "streaming client ready: count=%ju period_ms=%ju\n", (uintmax_t)count, (uintmax_t)period_ms);

    // Run the event loop forever.
    while (true) {
        const cy_err_t err_spin = cy_spin_once(cy);
        if (err_spin != CY_OK) {
            (void)fprintf(stderr, "cy_spin_once: %d\n", err_spin);
            break;
        }
        if (((state.received + 1U) == state.expected) && (future != NULL)) {
            (void)fprintf(stderr, "intentionally stopping early, the server will know\n");
            cy_future_destroy(future);
            future = NULL;
        }
    }
    return 0;
}
