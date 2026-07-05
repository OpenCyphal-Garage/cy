// Shared fixture for intrusive tests that drive the real cy_on_message() path and inspect internals.
// Include only after <cy.c>; requires linking message.c.
#pragma once

#include <unity.h>
#include "guarded_heap.h"
#include "message.h"
#include "intrusive_fixture_utils.h"
#include <string.h>

#define ACK_CAPTURE_CAPACITY 32U

typedef struct
{
    byte_t   type;
    uint64_t tag;
    uint64_t hash;
} ack_capture_t;

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    guarded_heap_t       heap;
    cy_t*                cy;
    cy_us_t              now;
    uint64_t             rand_state;

    size_t fail_after;      ///< Fail N-th new allocation when new_alloc_count >= fail_after.
    size_t new_alloc_count; ///< Counts fresh allocations only.

    size_t        ack_count;
    ack_capture_t acks[ACK_CAPTURE_CAPACITY];

    subject_tracker_t active_readers;
    subject_tracker_t active_writers;
} msg_fixture_t;

static inline void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    msg_fixture_t* const self = (msg_fixture_t*)platform;
    if ((ptr == NULL) && (size > 0U)) {
        if (self->new_alloc_count >= self->fail_after) {
            return NULL;
        }
        self->new_alloc_count++;
    }
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static inline cy_us_t fixture_now(cy_platform_t* const platform) { return ((msg_fixture_t*)platform)->now; }

static inline uint64_t fixture_random(cy_platform_t* const platform)
{
    return intrusive_random_lcg(&((msg_fixture_t*)platform)->rand_state);
}

static inline void fixture_unicast_extent_set(cy_platform_t* const platform, const size_t extent)
{
    (void)platform;
    (void)extent;
}

static inline cy_err_t fixture_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    (void)platform;
    (void)deadline;
    return CY_OK;
}

static inline cy_subject_writer_t* fixture_subject_writer_new(cy_platform_t* const platform, const uint32_t subject_id)
{
    msg_fixture_t* const       self = (msg_fixture_t*)platform;
    cy_subject_writer_t* const out  = intrusive_subject_writer_new(&self->heap, subject_id);
    if (out != NULL) {
        subject_tracker_add(&self->active_writers, subject_id);
    }
    return out;
}

static inline void fixture_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    msg_fixture_t* const self = (msg_fixture_t*)platform;
    subject_tracker_remove(&self->active_writers, writer->subject_id);
    intrusive_subject_writer_destroy(&self->heap, writer);
}

static inline cy_err_t fixture_subject_writer_send(cy_platform_t* const       platform,
                                                   cy_subject_writer_t* const writer,
                                                   const cy_us_t              deadline,
                                                   const cy_prio_t            priority,
                                                   const cy_bytes_t           message)
{
    (void)platform;
    (void)writer;
    (void)deadline;
    (void)priority;
    (void)message;
    return CY_OK;
}

static inline cy_subject_reader_t* fixture_subject_reader_new(cy_platform_t* const platform,
                                                              const uint32_t       subject_id,
                                                              const size_t         extent)
{
    msg_fixture_t* const       self = (msg_fixture_t*)platform;
    cy_subject_reader_t* const out  = intrusive_subject_reader_new(&self->heap, subject_id, extent);
    if (out != NULL) {
        subject_tracker_add(&self->active_readers, subject_id);
    }
    return out;
}

static inline void fixture_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    msg_fixture_t* const self = (msg_fixture_t*)platform;
    subject_tracker_remove(&self->active_readers, reader->subject_id);
    intrusive_subject_reader_destroy(&self->heap, reader);
}

static inline void fixture_subject_reader_extent_set(cy_platform_t* const       platform,
                                                     cy_subject_reader_t* const reader,
                                                     const size_t               extent)
{
    msg_fixture_t* const self = (msg_fixture_t*)platform;
    subject_tracker_assert_contains(&self->active_readers, reader->subject_id);
    intrusive_subject_reader_extent_set(reader, extent);
}

// Captures outbound ACK/NACK frames so tests can assert exactly what the stack acknowledged.
static inline cy_err_t fixture_unicast_send(cy_platform_t* const   platform,
                                            const cy_lane_t* const lane,
                                            const cy_us_t          deadline,
                                            const cy_bytes_t       message)
{
    (void)lane;
    (void)deadline;
    msg_fixture_t* const self                 = (msg_fixture_t*)platform;
    byte_t               header[HEADER_BYTES] = { 0 };
    size_t               copied               = 0U;
    const cy_bytes_t*    frag                 = &message;
    while ((frag != NULL) && (copied < sizeof(header))) {
        if ((frag->size > 0U) && (frag->data != NULL)) {
            const size_t n = smaller(sizeof(header) - copied, frag->size);
            memcpy(&header[copied], frag->data, n);
            copied += n;
        }
        frag = frag->next;
    }
    if ((copied >= HEADER_BYTES) && ((header[0] == header_msg_ack) || (header[0] == header_msg_nack)) && //
        (self->ack_count < ACK_CAPTURE_CAPACITY)) {
        ack_capture_t* const ack = &self->acks[self->ack_count++];
        ack->type                = header[0];
        ack->hash                = deserialize_u64(&header[8]);
        ack->tag                 = deserialize_u64(&header[16]);
    }
    return CY_OK;
}

static inline void fixture_init(msg_fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0x0BADC0DE12345678));
    self->platform.vtable                  = &self->vtable;
    self->platform.subject_id_modulus      = (uint32_t)CY_SUBJECT_ID_MODULUS_16bit;
    self->vtable.subject_writer_new        = fixture_subject_writer_new;
    self->vtable.subject_writer_destroy    = fixture_subject_writer_destroy;
    self->vtable.subject_writer_send       = fixture_subject_writer_send;
    self->vtable.subject_reader_new        = fixture_subject_reader_new;
    self->vtable.subject_reader_destroy    = fixture_subject_reader_destroy;
    self->vtable.subject_reader_extent_set = fixture_subject_reader_extent_set;
    self->vtable.unicast                   = fixture_unicast_send;
    self->vtable.unicast_extent_set        = fixture_unicast_extent_set;
    self->vtable.spin                      = fixture_spin;
    self->vtable.now                       = fixture_now;
    self->vtable.realloc                   = fixture_realloc;
    self->vtable.random                    = fixture_random;
    self->now                              = 1000000;
    self->rand_state                       = UINT64_C(0xFEEDFACECAFEBEEF);
    self->fail_after                       = SIZE_MAX;
    self->cy                               = cy_new(&self->platform, cy_str("home"), cy_str(""), cy_str(""));
    TEST_ASSERT_NOT_NULL(self->cy);
}

static inline void fixture_advance_to(msg_fixture_t* const self, const cy_us_t now)
{
    TEST_ASSERT_TRUE(now >= self->now);
    self->now = now;
    (void)olga_spin(&self->cy->olga);
}

static inline void fixture_teardown(msg_fixture_t* const self)
{
    fixture_advance_to(self, self->now + 1); // Let deferred destructions run.
    cy_destroy(self->cy);
    self->cy = NULL;
    intrusive_assert_heap_clean(&self->heap);
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
}

// Injects a message (best-effort or reliable) into the stack via the unicast path, as if received from a remote.
// Unicast is used because it skips the inline-gossip subject-ID consistency check, simplifying the setup.
static inline void inject_message_from(msg_fixture_t* const    self,
                                       const cy_topic_t* const topic,
                                       const uint64_t          remote_id,
                                       const bool              reliable,
                                       const uint64_t          tag,
                                       const byte_t            marker)
{
    byte_t wire[HEADER_BYTES + 4U] = { reliable ? header_msg_rel : header_msg_be, 0, 0, 0xFF /* lage=-1 */ };
    (void)serialize_u32(&wire[4], topic->evictions);
    (void)serialize_u64(&wire[8], topic->hash);
    (void)serialize_u64(&wire[16], tag);
    wire[HEADER_BYTES + 0U] = marker;
    wire[HEADER_BYTES + 1U] = (byte_t)(marker + 1U);
    wire[HEADER_BYTES + 2U] = (byte_t)(marker + 2U);
    wire[HEADER_BYTES + 3U] = (byte_t)(marker + 3U);
    cy_message_t* const msg = cy_test_message_make(&self->heap, wire, sizeof(wire));
    TEST_ASSERT_NOT_NULL(msg);
    cy_lane_t lane            = { 0 };
    lane.id                   = remote_id;
    lane.prio                 = cy_prio_nominal;
    const cy_message_ts_t mts = { .timestamp = self->now, .content = msg };
    cy_on_message(&self->platform, lane, NULL, mts);
}

static inline void inject_message(msg_fixture_t* const    self,
                                  const cy_topic_t* const topic,
                                  const bool              reliable,
                                  const uint64_t          tag,
                                  const byte_t            marker)
{
    inject_message_from(self, topic, UINT64_C(0xBEEF), reliable, tag, marker);
}

// Finds a reordering state by (remote-ID, topic) in the subscriber's index, or NULL if absent.
static inline cy_tree_t* find_reordering_state(subscriber_t* const sub,
                                               cy_topic_t* const   topic,
                                               const uint64_t      remote_id)
{
    reordering_context_t key = { 0 };
    key.lane.id              = remote_id;
    key.topic                = topic;
    return cavl2_find(sub->index_reordering_by_remote_id, &key, reordering_cavl_compare);
}

static inline dedup_t* find_dedup(cy_topic_t* const topic, const uint64_t remote_id)
{
    return CAVL2_TO_OWNER(
      cavl2_find(topic->sub_index_dedup_by_remote_id, &remote_id, dedup_cavl_compare), dedup_t, index_remote_id);
}

// Number of captured ACK/NACK frames carrying the given tag.
static inline size_t count_acks_with_tag(const msg_fixture_t* const self, const uint64_t tag)
{
    size_t n = 0U;
    for (size_t i = 0U; i < self->ack_count; i++) {
        if (self->acks[i].tag == tag) {
            n++;
        }
    }
    return n;
}

// The single live subscriber coupled to the topic (there is exactly one in these tests).
static inline subscriber_t* topic_only_subscriber(cy_topic_t* const topic)
{
    TEST_ASSERT_NOT_NULL(topic->couplings);
    subscriber_t* const sub = topic->couplings->root->head;
    TEST_ASSERT_NOT_NULL(sub);
    return sub;
}
