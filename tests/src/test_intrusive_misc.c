#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include <string.h>

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    cy_t                 cy;
    guarded_heap_t       heap;

    size_t fail_after;      ///< Fail N-th new allocation if new_alloc_count >= fail_after.
    size_t new_alloc_count; ///< Counts new allocations only, excludes realloc/free.
} fixture_t;

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    fixture_t* const self = (fixture_t*)platform;
    if ((ptr == NULL) && (size > 0U)) {
        if (self->new_alloc_count >= self->fail_after) {
            return NULL;
        }
        self->new_alloc_count++;
    }
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0xB17E5D0C1234ABCD));
    self->platform.vtable             = &self->vtable;
    self->platform.subject_id_modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    self->platform.cy                 = &self->cy;
    self->vtable.realloc              = fixture_realloc;
    self->cy.platform                 = &self->platform;
    self->fail_after                  = SIZE_MAX;
    self->new_alloc_count             = 0;
}

static void fixture_set_fail_after(fixture_t* const self, const size_t fail_after)
{
    self->fail_after      = fail_after;
    self->new_alloc_count = 0;
}

static size_t expected_chunk_count(const size_t payload_size)
{
    const size_t chunk = BYTES_DUP_CHUNK - sizeof(cy_bytes_t);
    return (payload_size == 0U) ? 0U : (1U + ((payload_size - 1U) / chunk));
}

static void fill_payload(unsigned char* const out, const size_t size)
{
    for (size_t i = 0U; i < size; i++) {
        out[i] = (unsigned char)((i * 73U) ^ (i >> 3U));
    }
}

static cy_bytes_t build_source(const unsigned char* const payload,
                               const size_t               total_size,
                               const size_t               fragment_count,
                               const size_t* const        fragment_sizes,
                               cy_bytes_t* const          out_fragments)
{
    assert(fragment_count > 0U);
    assert(out_fragments != NULL);
    size_t offset = 0U;
    for (size_t i = 0U; i < fragment_count; i++) {
        const size_t frag_size = fragment_sizes[i];
        TEST_ASSERT_TRUE(offset <= total_size);
        TEST_ASSERT_TRUE(frag_size <= (total_size - offset));
        out_fragments[i].size = frag_size;
        out_fragments[i].data = (frag_size > 0U) ? (const void*)&payload[offset] : NULL;
        out_fragments[i].next = (i + 1U < fragment_count) ? &out_fragments[i + 1U] : NULL;
        offset += frag_size;
    }
    TEST_ASSERT_EQUAL_size_t(total_size, offset);
    return out_fragments[0];
}

static void assert_duplicated_chain(const unsigned char* const payload,
                                    const size_t               payload_size,
                                    const cy_bytes_t*          duplicated)
{
    if (payload_size == 0) {
        TEST_ASSERT_TRUE(duplicated == &bytes_empty_sentinel);
        return;
    }
    const size_t chunk  = BYTES_DUP_CHUNK - sizeof(cy_bytes_t);
    size_t       copied = 0U;
    size_t       count  = 0U;
    while (duplicated != NULL) {
        count++;
        TEST_ASSERT_TRUE(duplicated->data == (const void*)(duplicated + 1));
        if (duplicated->next == NULL) {
            TEST_ASSERT_TRUE(duplicated->size <= chunk);
        } else {
            TEST_ASSERT_EQUAL_size_t(chunk, duplicated->size);
        }
        if (duplicated->size > 0U) {
            TEST_ASSERT_EQUAL_MEMORY(&payload[copied], duplicated->data, duplicated->size);
        }
        copied += duplicated->size;
        duplicated = duplicated->next;
    }
    TEST_ASSERT_EQUAL_size_t(payload_size, copied);
    TEST_ASSERT_EQUAL_size_t(expected_chunk_count(payload_size), count);
}

#define FRAGMENT_MAX 3U
#define PAYLOAD_MAX  (((BYTES_DUP_CHUNK) * 3U) + 8U)

static void run_case(fixture_t* const fixture,
                     const size_t     payload_size,
                     const size_t     fragment_count,
                     const size_t*    fragment_sizes)
{
    TEST_ASSERT_TRUE(fragment_count > 0U);
    TEST_ASSERT_TRUE(fragment_count <= FRAGMENT_MAX);
    TEST_ASSERT_TRUE(payload_size <= PAYLOAD_MAX);

    unsigned char payload[PAYLOAD_MAX] = { 0 };
    fill_payload(payload, payload_size);

    cy_bytes_t       fragments[FRAGMENT_MAX];
    const cy_bytes_t source = build_source(payload, payload_size, fragment_count, fragment_sizes, fragments);

    fixture_set_fail_after(fixture, SIZE_MAX);
    const cy_bytes_t* const duplicated = bytes_dup(&fixture->cy, source);

    const size_t chunk_count = expected_chunk_count(payload_size);
    TEST_ASSERT_NOT_NULL(duplicated);
    assert_duplicated_chain(payload, payload_size, duplicated);
    TEST_ASSERT_EQUAL_size_t(chunk_count, guarded_heap_allocated_fragments(&fixture->heap));
    TEST_ASSERT_EQUAL_size_t(chunk_count * BYTES_DUP_CHUNK, guarded_heap_allocated_bytes(&fixture->heap));

    bytes_undup(&fixture->cy, duplicated);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture->heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture->heap));
}

static void run_two_fragment_exhaustive(fixture_t* const fixture, const size_t min_size, const size_t max_size)
{
    for (size_t total = min_size; total <= max_size; total++) {
        for (size_t left = 0U; left <= total; left++) {
            const size_t sizes[2] = { left, total - left };
            run_case(fixture, total, 2U, sizes);
        }
    }
}

static void test_bytes_dup_undup_single_fragment_exhaustive_sizes(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const size_t max_size = ((BYTES_DUP_CHUNK - sizeof(cy_bytes_t)) * 2U) + 3U;
    for (size_t total = 0U; total <= max_size; total++) {
        const size_t sizes[1] = { total };
        run_case(&fixture, total, 1U, sizes);
    }
}

static void test_bytes_dup_undup_two_fragments_exhaustive_splits(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    run_two_fragment_exhaustive(&fixture, 0U, 64U);

    const size_t chunk        = BYTES_DUP_CHUNK - sizeof(cy_bytes_t);
    const size_t near_one_min = (chunk > 3U) ? (chunk - 3U) : 0U;
    const size_t near_one_max = chunk + 3U;
    const size_t near_two_min = (chunk * 2U > 3U) ? ((chunk * 2U) - 3U) : 0U;
    const size_t near_two_max = (chunk * 2U) + 3U;
    run_two_fragment_exhaustive(&fixture, near_one_min, near_one_max);
    run_two_fragment_exhaustive(&fixture, near_two_min, near_two_max);
}

static void test_bytes_dup_undup_three_fragments_exhaustive_small_sizes(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    for (size_t total = 0U; total <= 24U; total++) {
        for (size_t first = 0U; first <= total; first++) {
            for (size_t second = 0U; second <= (total - first); second++) {
                const size_t third   = total - first - second;
                const size_t sizes[] = { first, second, third };
                run_case(&fixture, total, 3U, sizes);
            }
        }
    }
}

static void test_bytes_dup_oom_cleans_up_partial_chain(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const size_t total_size  = ((BYTES_DUP_CHUNK - sizeof(cy_bytes_t)) * 3U) + 1U;
    const size_t chunk_count = expected_chunk_count(total_size);
    TEST_ASSERT_TRUE(chunk_count > 1U);

    unsigned char payload[PAYLOAD_MAX] = { 0 };
    fill_payload(payload, total_size);

    const size_t     first_size = (BYTES_DUP_CHUNK - sizeof(cy_bytes_t)) + 1U;
    const size_t     sizes[2]   = { first_size, total_size - first_size };
    cy_bytes_t       fragments[2];
    const cy_bytes_t source = build_source(payload, total_size, 2U, sizes, fragments);

    for (size_t fail_after = 0U; fail_after < chunk_count; fail_after++) {
        fixture_set_fail_after(&fixture, fail_after);
        const cy_bytes_t* const duplicated = bytes_dup(&fixture.cy, source);
        TEST_ASSERT_NULL(duplicated);
        TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
        TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
    }
}

static void test_bytes_undup_null_is_noop(void)
{
    fixture_t fixture;
    fixture_init(&fixture);
    bytes_undup(&fixture.cy, NULL);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

static size_t bitmap_clz_reference(const bitmap_t* const bitmap, const size_t count)
{
    for (size_t i = 0U; i < count; i++) {
        if (bitmap_test(bitmap, i)) {
            return i;
        }
    }
    return count;
}

static void test_bitmap_clz_basic(void)
{
    bitmap_t bm[3] = { 0, 0, 0 };

    TEST_ASSERT_EQUAL_size_t(0U, bitmap_clz(NULL, 0U));
    TEST_ASSERT_EQUAL_size_t(5U, bitmap_clz(NULL, 5U));
    TEST_ASSERT_EQUAL_size_t(0U, bitmap_clz(bm, 0U));
    TEST_ASSERT_EQUAL_size_t(130U, bitmap_clz(bm, 130U));

    bitmap_set(bm, 0U);
    TEST_ASSERT_EQUAL_size_t(0U, bitmap_clz(bm, 130U));

    bitmap_clear(bm, 0U);
    bitmap_set(bm, 64U);
    TEST_ASSERT_EQUAL_size_t(64U, bitmap_clz(bm, 130U));

    bitmap_set(bm, 2U);
    TEST_ASSERT_EQUAL_size_t(2U, bitmap_clz(bm, 130U));
}

static void test_bitmap_clz_ignores_tail_padding_bits(void)
{
    bitmap_t bm[2] = { 0, 0 };

    // count=65 means only bits 0..64 are valid.
    bm[1] = UINT64_C(1) << 1U; // global bit 65 (out of range)
    TEST_ASSERT_EQUAL_size_t(65U, bitmap_clz(bm, 65U));

    bm[1] = UINT64_C(1) << 0U; // global bit 64 (in range)
    TEST_ASSERT_EQUAL_size_t(64U, bitmap_clz(bm, 65U));
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_bytes_dup_undup_single_fragment_exhaustive_sizes);
    RUN_TEST(test_bytes_dup_undup_two_fragments_exhaustive_splits);
    RUN_TEST(test_bytes_dup_undup_three_fragments_exhaustive_small_sizes);
    RUN_TEST(test_bytes_dup_oom_cleans_up_partial_chain);
    RUN_TEST(test_bytes_undup_null_is_noop);
    RUN_TEST(test_bitmap_clz_basic);
    RUN_TEST(test_bitmap_clz_ignores_tail_padding_bits);
    return UNITY_END();
}
