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
        out->extent          = extent;
    }
    return (out != NULL) ? &out->base : NULL;
}

static inline void intrusive_subject_reader_destroy(guarded_heap_t* const heap, cy_subject_reader_t* const reader)
{
    guarded_heap_free(heap, reader);
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
