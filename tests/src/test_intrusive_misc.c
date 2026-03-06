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
    uint64_t             random_state;

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

static uint64_t fixture_random(cy_platform_t* const platform)
{
    fixture_t* const self = (fixture_t*)platform;
    self->random_state    = (self->random_state * UINT64_C(6364136223846793005)) + UINT64_C(1);
    return self->random_state;
}

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0xB17E5D0C1234ABCD));
    self->platform.vtable             = &self->vtable;
    self->platform.subject_id_modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    self->platform.cy                 = &self->cy;
    self->vtable.realloc              = fixture_realloc;
    self->vtable.random               = fixture_random;
    self->cy.platform                 = &self->platform;
    self->random_state                = UINT64_C(0x123456789ABCDEF0);
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

static void test_bytes_dup_all_empty_fragments_returns_sentinel(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    static const unsigned char dummy = 0xA5U;
    cy_bytes_t                 fragments[3];
    memset(fragments, 0, sizeof(fragments));
    fragments[0].size = 0U;
    fragments[0].data = &dummy;
    fragments[0].next = &fragments[1];
    fragments[1].size = 0U;
    fragments[1].data = NULL;
    fragments[1].next = &fragments[2];
    fragments[2].size = 0U;
    fragments[2].data = &dummy;
    fragments[2].next = NULL;

    const cy_bytes_t* const duplicated = bytes_dup(&fixture.cy, fragments[0]);
    TEST_ASSERT_TRUE(duplicated == &bytes_empty_sentinel);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));

    bytes_undup(&fixture.cy, duplicated);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_bytes_dup_oom_before_first_chunk(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    static const unsigned char payload = 0x5AU;
    const cy_bytes_t           source  = { .size = 1U, .data = &payload, .next = NULL };

    fixture_set_fail_after(&fixture, 0U);
    const cy_bytes_t* const duplicated = bytes_dup(&fixture.cy, source);
    TEST_ASSERT_NULL(duplicated);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

static bool bitmap_ref_test(const bitmap_t* const bitmap, const size_t bit)
{
    return (bitmap[bit / 64U] & (UINT64_C(1) << (bit % 64U))) != 0U;
}

static void bitmap_ref_set(bitmap_t* const bitmap, const size_t bit)
{
    bitmap[bit / 64U] |= UINT64_C(1) << (bit % 64U);
}

static void bitmap_ref_shift(bitmap_t* const       out,
                             const bitmap_t* const in,
                             const size_t          bit_count,
                             const ptrdiff_t       shift_amount)
{
    const size_t words = BITMAP_WORDS(bit_count);
    memset(out, 0, words * sizeof(out[0]));
    if ((bit_count == 0U) || (shift_amount == 0)) {
        memcpy(out, in, words * sizeof(out[0]));
        return;
    }
    for (size_t dst = 0U; dst < bit_count; dst++) {
        const ptrdiff_t src = (ptrdiff_t)dst - shift_amount;
        if ((src >= 0) && ((size_t)src < bit_count) && bitmap_ref_test(in, (size_t)src)) {
            bitmap_ref_set(out, dst);
        }
    }
}

static void assert_bitmap_words_equal(const bitmap_t* const expected,
                                      const bitmap_t* const actual,
                                      const size_t          bit_count)
{
    const size_t words = BITMAP_WORDS(bit_count);
    for (size_t i = 0U; i < words; i++) {
        TEST_ASSERT_EQUAL_UINT64(expected[i], actual[i]);
    }
}

static void assert_bitmap_shift_case(const size_t    bit_count,
                                     const ptrdiff_t shift_amount,
                                     const bitmap_t  word0,
                                     const bitmap_t  word1,
                                     const bitmap_t  word2)
{
    bitmap_t source[3]   = { word0, word1, word2 };
    bitmap_t actual[3]   = { word0, word1, word2 };
    bitmap_t expected[3] = { 0, 0, 0 };
    bitmap_ref_shift(expected, source, bit_count, shift_amount);
    bitmap_shift(actual, bit_count, shift_amount);
    assert_bitmap_words_equal(expected, actual, bit_count);
}

static void test_bitmap_footprint_rounding(void)
{
    TEST_ASSERT_EQUAL_size_t(0U, bitmap_footprint(0U));
    TEST_ASSERT_EQUAL_size_t(sizeof(bitmap_t), bitmap_footprint(1U));
    TEST_ASSERT_EQUAL_size_t(sizeof(bitmap_t), bitmap_footprint(63U));
    TEST_ASSERT_EQUAL_size_t(sizeof(bitmap_t), bitmap_footprint(64U));
    TEST_ASSERT_EQUAL_size_t(2U * sizeof(bitmap_t), bitmap_footprint(65U));
    TEST_ASSERT_EQUAL_size_t(3U * sizeof(bitmap_t), bitmap_footprint(130U));
}

static void test_bitmap_new_zero_init_and_oom(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    fixture_set_fail_after(&fixture, SIZE_MAX);
    bitmap_t* const bm = bitmap_new(&fixture.cy, 130U);
    TEST_ASSERT_NOT_NULL(bm);
    TEST_ASSERT_EQUAL_size_t(1U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(bitmap_footprint(130U), guarded_heap_allocated_bytes(&fixture.heap));
    for (size_t i = 0U; i < BITMAP_WORDS(130U); i++) {
        TEST_ASSERT_EQUAL_UINT64(0U, bm[i]);
    }
    mem_free(&fixture.cy, bm);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));

    fixture_set_fail_after(&fixture, SIZE_MAX);
    TEST_ASSERT_NULL(bitmap_new(&fixture.cy, 0U));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));

    fixture_set_fail_after(&fixture, 0U);
    TEST_ASSERT_NULL(bitmap_new(&fixture.cy, 1U));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_bitmap_set_clear_test_cross_word(void)
{
    bitmap_t bm[3] = { 0, 0, 0 };

    TEST_ASSERT_FALSE(bitmap_test(bm, 0U));
    TEST_ASSERT_FALSE(bitmap_test(bm, 63U));
    TEST_ASSERT_FALSE(bitmap_test(bm, 64U));
    TEST_ASSERT_FALSE(bitmap_test(bm, 129U));

    bitmap_set(bm, 0U);
    bitmap_set(bm, 63U);
    bitmap_set(bm, 64U);
    bitmap_set(bm, 129U);

    TEST_ASSERT_TRUE(bitmap_test(bm, 0U));
    TEST_ASSERT_TRUE(bitmap_test(bm, 63U));
    TEST_ASSERT_TRUE(bitmap_test(bm, 64U));
    TEST_ASSERT_TRUE(bitmap_test(bm, 129U));
    TEST_ASSERT_FALSE(bitmap_test(bm, 1U));
    TEST_ASSERT_FALSE(bitmap_test(bm, 65U));

    bitmap_clear(bm, 63U);
    bitmap_clear(bm, 129U);
    TEST_ASSERT_TRUE(bitmap_test(bm, 0U));
    TEST_ASSERT_FALSE(bitmap_test(bm, 63U));
    TEST_ASSERT_TRUE(bitmap_test(bm, 64U));
    TEST_ASSERT_FALSE(bitmap_test(bm, 129U));
}

static void test_bitmap_clz_branch_matrix(void)
{
    bitmap_t bm130[3] = { 0, 0, 0 };
    bitmap_t bm128[2] = { 0, 0 };
    bitmap_t bm65[2]  = { 0, 0 };

    TEST_ASSERT_EQUAL_size_t(5U, bitmap_clz(NULL, 5U));
    TEST_ASSERT_EQUAL_size_t(0U, bitmap_clz(bm130, 0U));
    TEST_ASSERT_EQUAL_size_t(130U, bitmap_clz(bm130, 130U));

    bm130[1] = UINT64_C(1) << 7U; // bit 71.
    TEST_ASSERT_EQUAL_size_t(71U, bitmap_clz(bm130, 130U));

    bm130[0] = UINT64_C(1) << 3U; // first word now wins.
    TEST_ASSERT_EQUAL_size_t(3U, bitmap_clz(bm130, 130U));

    bm130[0] = 0U;
    bm130[1] = 0U;
    bm130[2] = UINT64_C(1) << 1U; // bit 129.
    TEST_ASSERT_EQUAL_size_t(129U, bitmap_clz(bm130, 130U));

    bm65[1] = UINT64_C(1) << 1U; // bit 65 is outside count=65.
    TEST_ASSERT_EQUAL_size_t(65U, bitmap_clz(bm65, 65U));
    bm65[1] = UINT64_C(1) << 0U; // bit 64 is valid.
    TEST_ASSERT_EQUAL_size_t(64U, bitmap_clz(bm65, 65U));

    bm128[1] = UINT64_C(1) << 5U; // tail=0 path (bit count is multiple of 64).
    TEST_ASSERT_EQUAL_size_t(69U, bitmap_clz(bm128, 128U));
}

static void test_bitmap_any_none_branch_matrix(void)
{
    bitmap_t bm130[3] = { 0, 0, 0 };
    bitmap_t bm65[2]  = { 0, 0 };
    bitmap_t bm128[2] = { 0, 0 };

    TEST_ASSERT_FALSE(bitmap_any(NULL, 5U));
    TEST_ASSERT_TRUE(bitmap_none(NULL, 5U));

    TEST_ASSERT_FALSE(bitmap_any(bm130, 0U));
    TEST_ASSERT_TRUE(bitmap_none(bm130, 0U));
    TEST_ASSERT_FALSE(bitmap_any(bm130, 130U));
    TEST_ASSERT_TRUE(bitmap_none(bm130, 130U));

    bm130[0] = UINT64_C(1) << 11U;
    TEST_ASSERT_TRUE(bitmap_any(bm130, 130U));
    TEST_ASSERT_FALSE(bitmap_none(bm130, 130U));

    bm65[1] = UINT64_C(1) << 1U; // out-of-range for count=65.
    TEST_ASSERT_FALSE(bitmap_any(bm65, 65U));
    TEST_ASSERT_TRUE(bitmap_none(bm65, 65U));
    bm65[1] = UINT64_C(1) << 0U; // bit 64 is valid.
    TEST_ASSERT_TRUE(bitmap_any(bm65, 65U));
    TEST_ASSERT_FALSE(bitmap_none(bm65, 65U));

    bm128[1] = UINT64_C(1) << 63U; // tail=0 path.
    TEST_ASSERT_TRUE(bitmap_any(bm128, 128U));
    TEST_ASSERT_FALSE(bitmap_none(bm128, 128U));
}

static void test_bitmap_shift_guard_noop_paths(void)
{
    bitmap_t bm[3]       = { UINT64_C(0xAAAAAAAAAAAAAAAA), UINT64_C(0x0123456789ABCDEF), UINT64_C(0xFEDCBA9876543210) };
    bitmap_t snapshot[3] = { bm[0], bm[1], bm[2] };

    bitmap_shift(NULL, 130U, 1);

    bitmap_shift(bm, 0U, 1);
    TEST_ASSERT_EQUAL_UINT64(snapshot[0], bm[0]);
    TEST_ASSERT_EQUAL_UINT64(snapshot[1], bm[1]);
    TEST_ASSERT_EQUAL_UINT64(snapshot[2], bm[2]);

    bitmap_shift(bm, 130U, 0);
    TEST_ASSERT_EQUAL_UINT64(snapshot[0], bm[0]);
    TEST_ASSERT_EQUAL_UINT64(snapshot[1], bm[1]);
    TEST_ASSERT_EQUAL_UINT64(snapshot[2], bm[2]);
}

static void test_bitmap_shift_large_shift_clears_bitmap(void)
{
    bitmap_t bm[3] = { UINT64_C(0xAAAAAAAAAAAAAAAA), UINT64_C(0x0123456789ABCDEF), UINT64_C(0xFFFFFFFFFFFFFFFF) };

    bitmap_shift(bm, 130U, 130);
    TEST_ASSERT_EQUAL_UINT64(0U, bm[0]);
    TEST_ASSERT_EQUAL_UINT64(0U, bm[1]);
    TEST_ASSERT_EQUAL_UINT64(0U, bm[2]);

    bm[0] = UINT64_C(0xAAAAAAAAAAAAAAAA);
    bm[1] = UINT64_C(0x0123456789ABCDEF);
    bm[2] = UINT64_C(0xFFFFFFFFFFFFFFFF);
    bitmap_shift(bm, 130U, -130);
    TEST_ASSERT_EQUAL_UINT64(0U, bm[0]);
    TEST_ASSERT_EQUAL_UINT64(0U, bm[1]);
    TEST_ASSERT_EQUAL_UINT64(0U, bm[2]);
}

static void test_bitmap_shift_left_branch_matrix(void)
{
    const bitmap_t word0 = UINT64_C(0x0123456789ABCDEF);
    const bitmap_t word1 = UINT64_C(0x0FEDCBA987654321);
    const bitmap_t word2 = UINT64_C(0xFFFFFFFFFFFFFFFF);

    assert_bitmap_shift_case(130U, 1, word0, word1, word2);
    assert_bitmap_shift_case(130U, 64, word0, word1, word2);
    assert_bitmap_shift_case(130U, 65, word0, word1, word2);
    assert_bitmap_shift_case(128U, 1, word0, word1, word2);
    assert_bitmap_shift_case(128U, 64, word0, word1, word2);
}

static void test_bitmap_shift_right_branch_matrix(void)
{
    const bitmap_t word0 = UINT64_C(0x0123456789ABCDEF);
    const bitmap_t word1 = UINT64_C(0x0FEDCBA987654321);
    const bitmap_t word2 = UINT64_C(0xFFFFFFFFFFFFFFFF);

    assert_bitmap_shift_case(130U, -1, word0, word1, word2);
    assert_bitmap_shift_case(130U, -64, word0, word1, word2);
    assert_bitmap_shift_case(130U, -65, word0, word1, word2);
    assert_bitmap_shift_case(128U, -1, word0, word1, word2);
    assert_bitmap_shift_case(128U, -64, word0, word1, word2);
}

static void test_internal_helpers_branch_matrix(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    TEST_ASSERT_EQUAL_INT64(0, pow2us(-1));
    TEST_ASSERT_EQUAL_INT64(1, pow2us(0));
    TEST_ASSERT_EQUAL_INT64(INT64_MAX, pow2us(63));

    TEST_ASSERT_EQUAL_INT64(42, random_int(&fixture.cy, 42, 42));
    const int64_t rnd = random_int(&fixture.cy, -5, 5);
    TEST_ASSERT_TRUE((rnd >= -5) && (rnd < 5));

    TEST_ASSERT_FALSE(chance(&fixture.cy, 0U));
    TEST_ASSERT_TRUE(chance(&fixture.cy, 1U));

    TEST_ASSERT_EQUAL_size_t(0U, choice(&fixture.cy, 0U));
    TEST_ASSERT_TRUE(choice(&fixture.cy, 3U) < 3U);

#if CY_CONFIG_TRACE
    char     hex_buf[17] = { 0 };
    cy_str_t hex         = to_hex(UINT64_C(0x1A2B), 16U, hex_buf);
    TEST_ASSERT_EQUAL_size_t(4U, hex.len);
    TEST_ASSERT_EQUAL_MEMORY("1a2b", hex.str, hex.len);

    hex = to_hex(0U, 8U, NULL);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, hex.len);
    TEST_ASSERT_NULL(hex.str);
#endif

    bitmap_t bm[1] = { UINT64_C(0xFFFFFFFFFFFFFFFF) };
    bitmap_reset(NULL, 1U);
    bitmap_reset(bm, 1U);
    TEST_ASSERT_EQUAL_UINT64(0U, bm[0]);
    TEST_ASSERT_FALSE(bitmap_test_bounded(bm, 1U, 1U));

    TEST_ASSERT_FALSE(is_prime_u32(1U));
    TEST_ASSERT_TRUE(is_prime_u32(2U));
    TEST_ASSERT_FALSE(is_prime_u32(4U));
    TEST_ASSERT_FALSE(is_prime_u32(9U));
    TEST_ASSERT_TRUE(is_prime_u32(17U));
    TEST_ASSERT_TRUE(is_valid_subject_id_modulus((uint32_t)CY_SUBJECT_ID_MODULUS_17bit));
    TEST_ASSERT_FALSE(is_valid_subject_id_modulus(4U));
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
    RUN_TEST(test_bytes_dup_all_empty_fragments_returns_sentinel);
    RUN_TEST(test_bytes_dup_oom_before_first_chunk);
    RUN_TEST(test_bitmap_footprint_rounding);
    RUN_TEST(test_bitmap_new_zero_init_and_oom);
    RUN_TEST(test_bitmap_set_clear_test_cross_word);
    RUN_TEST(test_bitmap_clz_branch_matrix);
    RUN_TEST(test_bitmap_any_none_branch_matrix);
    RUN_TEST(test_bitmap_shift_guard_noop_paths);
    RUN_TEST(test_bitmap_shift_large_shift_clears_bitmap);
    RUN_TEST(test_bitmap_shift_left_branch_matrix);
    RUN_TEST(test_bitmap_shift_right_branch_matrix);
    RUN_TEST(test_internal_helpers_branch_matrix);
    return UNITY_END();
}
