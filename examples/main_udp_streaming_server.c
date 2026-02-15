// A tiny streaming server demo: receive a request and stream reliable responses.

#include "cy_udp_posix.h"
#include <rapidhash.h>

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#define TOPIC_NAME           "demo/stream"
#define RESPONSE_DEADLINE_us (2 * 1000000LL)
#define RESPONSE_MAX         128U
#define STREAM_MAX           8U

#define STREAM_ID_UNUSED 0ULL

// Request payload (little-endian, for demo simplicity).
typedef struct
{
    uint32_t count;
    uint32_t period_ms;
} stream_request_t;

typedef struct
{
    // Constant stream parameters.
    uint64_t        stream_id; ///< Precomputed for fast lookup; STREAM_ID_UNUSED if unused.
    cy_breadcrumb_t breadcrumb;
    cy_us_t         period_us;

    // Mutable stream state.
    cy_future_t* pending_response;
    uint32_t     remaining;
    cy_us_t      next_send_at;
} stream_state_t;

typedef struct
{
    stream_state_t* streams;
    size_t          count;
} stream_table_t;

static uint64_t make_stream_id(const cy_breadcrumb_t* const b)
{
    const uint64_t key[3] = { b->remote_id, b->topic_hash, b->transfer_id };
    return rapidhash(key, sizeof(key)); // collisions are astronomically unlikely; safe for all practical purposes
}

static stream_state_t* get_stream(stream_table_t* const table, const uint64_t stream_id)
{
    stream_state_t* free_slot = NULL;
    for (size_t i = 0; i < table->count; i++) {
        stream_state_t* const s = &table->streams[i];
        if (s->stream_id == stream_id) {
            return s;
        }
        if ((s->stream_id == STREAM_ID_UNUSED) && (free_slot == NULL)) {
            free_slot = s;
        }
    }
    return free_slot;
}

static void reset_stream(stream_state_t* const s)
{
    s->stream_id = STREAM_ID_UNUSED;
    s->period_us = 0;
    if (s->pending_response != NULL) {
        cy_future_destroy(s->pending_response); // Will cancel the in-flight response transfer, if any.
        s->pending_response = NULL;
    }
    s->remaining    = 0;
    s->next_send_at = 0;
}

static void on_response_future_update(cy_future_t* const future)
{
    assert(cy_future_status(future) != cy_future_pending); // the response future does not emit intermediate updates

    stream_state_t* const s = (stream_state_t*)cy_future_context(future).ptr[0];
    assert((s != NULL) && (s->pending_response == future));
    assert(s->remaining > 0);
    s->pending_response = NULL;

    const cy_response_result_t* const res = (const cy_response_result_t*)cy_future_result(future);
    if (cy_future_status(future) == cy_future_success) {
        s->remaining--;
        s->next_send_at = cy_now(s->breadcrumb.cy) + s->period_us;
        (void)fprintf(stderr,
                      "stream response delivered: stream_id=%016jx seqno=%ju remaining=%ju\n",
                      (uintmax_t)s->stream_id,
                      (uintmax_t)res->seqno,
                      (uintmax_t)s->remaining);
        if (s->remaining == 0) {
            (void)fprintf(stderr, "stream completed: stream_id=%016jx\n", (uintmax_t)s->stream_id);
            reset_stream(s);
        }
    } else {
        (void)fprintf(stderr,
                      "CLIENT UNREACHABLE, stopping stream_id=%016jx seqno=%ju remaining=%ju\n",
                      (uintmax_t)s->stream_id,
                      (uintmax_t)res->seqno,
                      (uintmax_t)s->remaining);
        reset_stream(s);
    }
    cy_future_destroy(future);
}

static void on_stream_request(cy_subscriber_t* const sub, cy_arrival_t* const arv)
{
    stream_table_t* const table = (stream_table_t*)cy_subscriber_context(sub).ptr[0];
    assert(table != NULL);
    assert((arv != NULL) && (arv->breadcrumb != NULL));

    // Parse the request payload and apply limits.
    stream_request_t req = { 0 };
    if (cy_message_read(&arv->message.content, 0, sizeof(req), &req) != sizeof(req)) {
        return; // malformed request -- payload too short, ignore
    }
    if (req.period_ms < 100) {
        req.period_ms = 100;
    }
    if (req.count == 0) {
        return; // nothing to do; the stream scheduler requires at least one message
    }

    // Find or allocate a stream slot for this stream ID.
    const uint64_t        stream_id = make_stream_id(arv->breadcrumb);
    stream_state_t* const s         = get_stream(table, stream_id);
    if (s == NULL) {
        (void)fprintf(stderr, "stream table full, dropping request\n");
        return;
    }

    // If this stream has already been in use, reset it with the new parameters.
    reset_stream(s);
    s->remaining    = req.count;
    s->period_us    = (cy_us_t)req.period_ms * 1000;
    s->next_send_at = cy_now(arv->breadcrumb->cy);
    s->stream_id    = stream_id;
    s->breadcrumb   = *arv->breadcrumb; // breadcrumb copied by value
    (void)fprintf(stderr,
                  "new stream: id=%016jx remote=%016jx topic=%016jx transfer=%016jx count=%ju period_ms=%ju\n",
                  (uintmax_t)s->stream_id,
                  (uintmax_t)s->breadcrumb.remote_id,
                  (uintmax_t)s->breadcrumb.topic_hash,
                  (uintmax_t)s->breadcrumb.transfer_id,
                  (uintmax_t)req.count,
                  (uintmax_t)req.period_ms);
}

int main(void)
{
    cy_udp_posix_t cy_udp;
    const cy_err_t res = cy_udp_posix_new_simple(&cy_udp);
    if (res != CY_OK) {
        (void)fprintf(stderr, "cy_udp_posix_new_simple: %jd\n", (intmax_t)res);
        return 1;
    }
    cy_t* const cy = &cy_udp.base;

    // Subscribe to the request topic.
    cy_subscriber_t* const sub = cy_subscribe(cy, cy_str(TOPIC_NAME), RESPONSE_MAX);
    if (sub == NULL) {
        (void)fprintf(stderr, "cy_subscribe: NULL\n");
        return 1;
    }

    // Set up the in-memory stream table and attach it to the subscriber context.
    stream_state_t streams[STREAM_MAX] = { 0 };
    stream_table_t table               = { .streams = streams, .count = STREAM_MAX };
    cy_subscriber_context_set(sub, (cy_user_context_t){ .ptr = { &table } });
    cy_subscriber_callback_set(sub, &on_stream_request);
    (void)fprintf(stderr, "streaming server ready on '%s'\n", TOPIC_NAME);

    // Run the event loop and emit responses at the requested cadence.
    while (true) {
        const cy_err_t err_spin = cy_udp_posix_spin_once(&cy_udp);
        if (err_spin != CY_OK) {
            (void)fprintf(stderr, "cy_udp_posix_spin_once: %jd\n", (intmax_t)err_spin);
            return 1;
        }

        // Drive all active streams.
        const cy_us_t now = cy_now(cy);
        for (size_t i = 0; i < table.count; i++) {
            stream_state_t* const s = &table.streams[i];
            if ((s->stream_id == STREAM_ID_UNUSED) || (now < s->next_send_at) || (s->pending_response != NULL)) {
                continue; // Empty slot, or not due yet, or response already in flight -- waiting for completion.
            }

            // Build a small text payload for the client.
            const uint64_t seq = s->breadcrumb.seqno;
            char           payload[RESPONSE_MAX];
            const int      len = snprintf(payload,
                                     sizeof(payload),
                                     "stream=%016jx seq=%ju time_us=%jd left=%ju",
                                     (uintmax_t)s->stream_id,
                                     (uintmax_t)seq,
                                     (intmax_t)now,
                                     (uintmax_t)s->remaining);
            assert(len > 0);
            const cy_bytes_t msg = { .size = (size_t)len, .data = payload };

            // Send the reliable response.
            s->pending_response = cy_respond_reliable(&s->breadcrumb, now + RESPONSE_DEADLINE_us, msg);
            if (s->pending_response == NULL) {
                (void)fprintf(stderr, "cy_respond_reliable: NULL\n");
                reset_stream(s);
                continue;
            }
            cy_future_context_set(s->pending_response, (cy_user_context_t){ .ptr = { s } });
            cy_future_callback_set(s->pending_response, &on_response_future_update);
        }
    }
    return 0;
}
