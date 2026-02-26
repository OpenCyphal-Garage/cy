#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

static bool bitset_get(const unsigned char* const bits, const uint32_t index)
{
    return (bits[index / 8U] & (unsigned char)(1U << (index % 8U))) != 0U;
}

static void bitset_set(unsigned char* const bits, const uint32_t index)
{
    bits[index / 8U] |= (unsigned char)(1U << (index % 8U));
}

// For non-pinned topics, the mapping differs only by additive translation with respect to hash residue.
// We can therefore test the quadratic progression properties at any one non-pinned hash.
static void check_subject_id_unique_until_half_modulus(const uint32_t modulus)
{
    const uint64_t hash = (uint64_t)CY_SUBJECT_ID_PINNED_MAX + 12345U;
    TEST_ASSERT(hash > CY_SUBJECT_ID_PINNED_MAX);
    const size_t         bitset_bytes = (CY_SUBJECT_ID_PINNED_MAX + modulus + 8U) / 8U;
    unsigned char* const seen_sid     = (unsigned char*)calloc(bitset_bytes, 1U);
    TEST_ASSERT_NOT_NULL(seen_sid);

    for (uint32_t evictions = 0U; evictions <= (modulus / 2U); evictions++) {
        const uint32_t subject_id = topic_subject_id_impl(hash, evictions, modulus);
        TEST_ASSERT(subject_id > CY_SUBJECT_ID_PINNED_MAX);
        TEST_ASSERT(subject_id <= CY_SUBJECT_ID_MAX(modulus));
        TEST_ASSERT(!bitset_get(seen_sid, subject_id));
        bitset_set(seen_sid, subject_id);
        if (evictions < 10) { // JFYI
            printf("hash=%ju evictions=%ju => subject_id=%ju\n",
                   (uintmax_t)hash,
                   (uintmax_t)evictions,
                   (uintmax_t)subject_id);
        }
    }

    free(seen_sid);
}

static void check_subject_id_threshold_repeat_exhaustive(const uint32_t modulus)
{
    const uint64_t hash = (uint64_t)CY_SUBJECT_ID_PINNED_MAX + 12345U;
    TEST_ASSERT(hash > CY_SUBJECT_ID_PINNED_MAX);
    const size_t         bitset_bytes = (CY_SUBJECT_ID_PINNED_MAX + modulus + 8U) / 8U;
    unsigned char* const seen_sid     = (unsigned char*)calloc(bitset_bytes, 1U);
    TEST_ASSERT_NOT_NULL(seen_sid);

    const uint32_t half = modulus / 2U;
    for (uint32_t evictions = 0U; evictions < modulus; evictions++) {
        const uint32_t subject_id = topic_subject_id_impl(hash, evictions, modulus);
        TEST_ASSERT(subject_id > CY_SUBJECT_ID_PINNED_MAX);
        TEST_ASSERT(subject_id <= CY_SUBJECT_ID_MAX(modulus));

        if (evictions <= half) {
            TEST_ASSERT(!bitset_get(seen_sid, subject_id));
            bitset_set(seen_sid, subject_id);
        } else {
            TEST_ASSERT(bitset_get(seen_sid, subject_id));
        }

        if (evictions > 0U) {
            const uint32_t mirror = modulus - evictions;
            TEST_ASSERT_EQUAL_UINT32(subject_id, topic_subject_id_impl(hash, mirror, modulus));
        }
    }
    TEST_ASSERT_EQUAL_UINT32(topic_subject_id_impl(hash, half, modulus),
                             topic_subject_id_impl(hash, half + 1U, modulus));
    free(seen_sid);
}

static uint32_t expected_subject_id_no_overflow(const uint64_t hash, const uint32_t evictions, const uint32_t modulus)
{
    TEST_ASSERT(hash > CY_SUBJECT_ID_PINNED_MAX);
    TEST_ASSERT(hash <= UINT32_MAX); // Avoid uint64 addition overflow in reference expression below.
    const uint64_t h = hash % modulus;
    const uint64_t e = ((uint64_t)evictions) % modulus;
    return (uint32_t)(CY_SUBJECT_ID_PINNED_MAX + 1ULL + ((h + ((e * e) % modulus)) % modulus));
}

static void check_subject_id_near_uint32_max(const uint32_t modulus)
{
    const uint64_t hash = UINT32_MAX;
    TEST_ASSERT(hash > CY_SUBJECT_ID_PINNED_MAX);
    for (uint64_t i = 0U; i < 65536U; i++) {
        const uint32_t evictions  = (uint32_t)(UINT32_MAX - i);
        const uint32_t subject_id = topic_subject_id_impl(hash, evictions, modulus);
        TEST_ASSERT_EQUAL_UINT32(expected_subject_id_no_overflow(hash, evictions, modulus), subject_id);
        TEST_ASSERT_EQUAL_UINT32(subject_id,
                                 topic_subject_id_impl(hash, (uint32_t)(((uint64_t)evictions) % modulus), modulus));
    }
}

static void test_subject_id_math_modulus_17bit(void)
{
    const uint32_t modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    check_subject_id_unique_until_half_modulus(modulus);
    check_subject_id_threshold_repeat_exhaustive(modulus);
    check_subject_id_near_uint32_max(modulus);
}

static void test_subject_id_math_modulus_23bit(void)
{
    const uint32_t modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_23bit;
    check_subject_id_unique_until_half_modulus(modulus);
    check_subject_id_threshold_repeat_exhaustive(modulus);
    check_subject_id_near_uint32_max(modulus);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_subject_id_math_modulus_17bit);
    RUN_TEST(test_subject_id_math_modulus_23bit);
    return UNITY_END();
}
