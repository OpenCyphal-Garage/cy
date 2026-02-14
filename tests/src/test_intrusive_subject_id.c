#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "helpers.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static bool bitset_get(const unsigned char* const bits, const uint32_t index)
{
    return (bits[index / 8U] & (unsigned char)(1U << (index % 8U))) != 0U;
}

static void bitset_set(unsigned char* const bits, const uint32_t index)
{
    bits[index / 8U] |= (unsigned char)(1U << (index % 8U));
}

/// For non-pinned topics, the subject-ID mapping is an additive translation by (hash % p), so it is sufficient to
/// exhaustively test injectivity and inversion at any single non-pinned hash. We sample one random hash per run.
static void check_subject_id_math(const uint32_t modulus)
{
    cy_t          cy       = { 0 };
    cy_platform_t platform = { .subject_id_modulus = modulus };
    cy.platform            = &platform;

    const uint64_t hash = prng();
    TEST_ASSERT(hash > CY_PINNED_SUBJECT_ID_MAX); // Otherwise it's just very bad luck!
    const size_t         bitset_bytes = (CY_PINNED_SUBJECT_ID_MAX + modulus + 7U) / 8U;
    unsigned char* const seen_sid     = (unsigned char*)calloc(bitset_bytes, 1U);
    TEST_ASSERT_NOT_NULL(seen_sid);

    for (uint32_t evictions = 0U; evictions <= (modulus / 2U); evictions++) {
        const uint32_t subject_id = topic_subject_id_impl(&cy, hash, evictions);
        TEST_ASSERT(subject_id > CY_PINNED_SUBJECT_ID_MAX);
        TEST_ASSERT(subject_id <= CY_PINNED_SUBJECT_ID_MAX + modulus);
        TEST_ASSERT(!bitset_get(seen_sid, subject_id));
        bitset_set(seen_sid, subject_id);
        TEST_ASSERT(evictions == topic_evictions_from_subject_id(hash, subject_id, modulus));
        if (evictions < 10) { // JFYI
            printf("hash=%llu evictions=%lu => subject_id=%lu\n",
                   (unsigned long long)hash,
                   (unsigned long)evictions,
                   (unsigned long)subject_id);
        }
    }

    free(seen_sid);
}

static void test_subject_id_math_modulus_17bit(void) { check_subject_id_math((uint32_t)CY_SUBJECT_ID_MODULUS_17bit); }

static void test_subject_id_math_modulus_23bit(void) { check_subject_id_math((uint32_t)CY_SUBJECT_ID_MODULUS_23bit); }

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_subject_id_math_modulus_17bit);
    RUN_TEST(test_subject_id_math_modulus_23bit);
    return UNITY_END();
}
