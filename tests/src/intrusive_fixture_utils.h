#pragma once

#include <cy_platform.h>
#include <unity.h>
#include "guarded_heap.h"
#include <stddef.h>
#include <stdint.h>

typedef struct
{
    cy_subject_writer_t base;
} intrusive_test_subject_writer_t;

typedef struct
{
    cy_subject_reader_t base;
    size_t              extent;
} intrusive_test_subject_reader_t;

static inline cy_subject_writer_t* intrusive_subject_writer_new(guarded_heap_t* const heap, const uint32_t subject_id)
{
    intrusive_test_subject_writer_t* const out =
      (intrusive_test_subject_writer_t*)guarded_heap_alloc(heap, sizeof(*out));
    if (out != NULL) {
        out->base.subject_id = subject_id;
    }
    return (out != NULL) ? &out->base : NULL;
}

static inline void intrusive_subject_writer_destroy(guarded_heap_t* const heap, cy_subject_writer_t* const writer)
{
    guarded_heap_free(heap, writer);
}

static inline cy_subject_reader_t* intrusive_subject_reader_new(guarded_heap_t* const heap,
                                                                const uint32_t        subject_id,
                                                                const size_t          extent)
{
    intrusive_test_subject_reader_t* const out =
      (intrusive_test_subject_reader_t*)guarded_heap_alloc(heap, sizeof(*out));
    if (out != NULL) {
        out->base.subject_id = subject_id;
        out->base.extent     = extent;
        out->extent          = extent;
    }
    return (out != NULL) ? &out->base : NULL;
}

static inline void intrusive_subject_reader_extent_set(cy_subject_reader_t* const reader, const size_t extent)
{
    intrusive_test_subject_reader_t* const r = (intrusive_test_subject_reader_t*)reader;
    reader->extent                           = extent;
    r->extent                                = extent;
}

static inline void intrusive_subject_reader_destroy(guarded_heap_t* const heap, cy_subject_reader_t* const reader)
{
    guarded_heap_free(heap, reader);
}

// Tracks active subject-IDs to assert the at-most-one-per-subject-ID platform guarantee.
#define SUBJECT_TRACKER_CAPACITY 256U

typedef struct
{
    uint32_t subject_ids[SUBJECT_TRACKER_CAPACITY];
    size_t   count;
} subject_tracker_t;

static inline void subject_tracker_add(subject_tracker_t* const t, const uint32_t subject_id)
{
    for (size_t i = 0; i < t->count; i++) {
        TEST_ASSERT_NOT_EQUAL_UINT32_MESSAGE(t->subject_ids[i], subject_id, "duplicate subject-ID");
    }
    TEST_ASSERT_TRUE_MESSAGE(t->count < SUBJECT_TRACKER_CAPACITY, "tracker full");
    t->subject_ids[t->count++] = subject_id;
}

static inline void subject_tracker_remove(subject_tracker_t* const t, const uint32_t subject_id)
{
    for (size_t i = 0; i < t->count; i++) {
        if (t->subject_ids[i] == subject_id) {
            t->subject_ids[i] = t->subject_ids[--t->count];
            return;
        }
    }
    TEST_FAIL_MESSAGE("subject_tracker_remove: subject-ID not found");
}

static inline void subject_tracker_assert_contains(const subject_tracker_t* const t, const uint32_t subject_id)
{
    for (size_t i = 0; i < t->count; i++) {
        if (t->subject_ids[i] == subject_id) {
            return;
        }
    }
    TEST_FAIL_MESSAGE("subject_tracker_assert_contains: subject-ID not found");
}

static inline uint64_t intrusive_random_lcg(uint64_t* const state)
{
    *state = (*state * UINT64_C(6364136223846793005)) + UINT64_C(1);
    return *state;
}

static inline void intrusive_assert_heap_clean(const guarded_heap_t* const heap)
{
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(heap));
}
