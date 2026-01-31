// A tiny streaming client demo: send one request and keep receiving responses.

#include "cy_udp_posix.h"

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
    uint32_t count;
    uint32_t period_ms;
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
    switch (cy_future_status(future)) {
        case cy_future_pending: {
            (void)fprintf(stderr, "request delivered, waiting for data stream...\n");
            break;
        }
        case cy_future_success: {
            cy_request_result_t* const res = (cy_request_result_t*)cy_future_result(future);
            char                       text[RESPONSE_MAX];
            const size_t               n = cy_message_read(&res->response.message.content, 0, RESPONSE_MAX - 1U, text);
            text[n]                      = '\0';
            (void)fprintf(stderr,
                          "response seq=%llu remote=%016llx: %s\n",
                          (unsigned long long)res->response.seqno,
                          (unsigned long long)res->response.remote_id,
                          text);
            st->received++;
            if (st->received >= st->expected) {
                st->done = true;
                // Once the future is destroyed, no further responses will be accepted; the server will observe failure
                // to deliver responses and terminate the stream.
                // We could also publish an explicit cancellation message, depending on the application requirements.
                cy_future_destroy(future);
            }
            break;
        }
        case cy_future_failure: {
            (void)fprintf(stderr, "request timed out\n");
            st->done = true;
            cy_future_destroy(future);
            break;
        }
    }
}

int main(const int argc, char* argv[])
{
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
    cy_udp_posix_t cy_udp;
    const cy_err_t res = cy_udp_posix_new_simple(&cy_udp);
    if (res != CY_OK) {
        (void)fprintf(stderr, "cy_udp_posix_new_simple: %d\n", res);
        return 1;
    }
    cy_t* const cy = &cy_udp.base;

    // Create the publisher that will issue the request.
    cy_publisher_t* const pub = cy_advertise_client(cy, wkv_key(TOPIC_NAME), RESPONSE_MAX);
    if (pub == NULL) {
        (void)fprintf(stderr, "cy_advertise_client: NULL\n");
        return 1;
    }

    // Send a single request that asks the server to stream responses.
    const stream_request_t req = { .count = count, .period_ms = period_ms };
    const cy_us_t          now = cy_now(cy);

    cy_future_t* const future = cy_request(pub,            //
                                           now + 10000000, // delivery deadline
                                           now + 20000000, // first response deadline
                                           (cy_bytes_t){ .size = sizeof(req), .data = &req });
    if (future == NULL) {
        (void)fprintf(stderr, "cy_request: NULL\n");
        return 1;
    }
    client_state_t state = { .expected = count, .received = 0, .done = false };
    cy_future_context_set(future, (cy_user_context_t){ .ptr = { &state } });
    cy_future_callback_set(future, &on_stream_response);
    (void)fprintf(stderr, "streaming client ready: count=%u period_ms=%u\n", count, period_ms);

    // Run the event loop until enough responses are received.
    while (!state.done) {
        const cy_err_t err_spin = cy_udp_posix_spin_once(&cy_udp);
        if (err_spin != CY_OK) {
            (void)fprintf(stderr, "cy_udp_posix_spin_once: %d\n", err_spin);
            break;
        }
    }
    return 0;
}
