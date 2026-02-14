#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "helpers.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define SUBJECT_ID_OFFSET (CY_PINNED_SUBJECT_ID_MAX + 1U)

typedef struct
{
    cy_t          cy;
    cy_platform_t platform;
} subject_id_fixture_t;

static bool bitset_get(const unsigned char* const bits, const uint32_t index)
{
    return (bits[index / 8U] & (unsigned char)(1U << (index % 8U))) != 0U;
}

static void bitset_set(unsigned char* const bits, const uint32_t index)
{
    bits[index / 8U] |= (unsigned char)(1U << (index % 8U));
}

static void subject_id_fixture_init(subject_id_fixture_t* const self, const uint32_t modulus)
{
    memset(self, 0, sizeof(*self));
    self->platform.subject_id_modulus = modulus;
    self->cy.platform                 = &self->platform;
}

static uint64_t random_non_pinned_hash(const uint32_t modulus)
{
    uint64_t seed = ((uint64_t)(uint32_t)time(NULL) << 32U) ^ (uint64_t)(uint32_t)clock() ^ modulus;
    if (seed == 0U) {
        seed = UINT64_C(0xD1B54A32D192ED03);
    }
    uint64_t out = 0;
    do {
        out = cy_test_prng_splitmix64_next(&seed);
    } while (out <= CY_PINNED_SUBJECT_ID_MAX);
    return out;
}

static void fail_check(const char* const reason,
                       const uint32_t    modulus,
                       const uint64_t    hash,
                       const uint32_t    evictions,
                       const uint32_t    subject_id,
                       const uint32_t    detail)
{
    char msg[256];
    (void)snprintf(msg,
                   sizeof(msg),
                   "%s: p=%lu hash=%llu evictions=%lu sid=%lu detail=%lu",
                   reason,
                   (unsigned long)modulus,
                   (unsigned long long)hash,
                   (unsigned long)evictions,
                   (unsigned long)subject_id,
                   (unsigned long)detail);
    TEST_FAIL_MESSAGE(msg);
}

/// For non-pinned topics, the subject-ID mapping is an additive translation by (hash % p), so it is sufficient to
/// exhaustively test injectivity and inversion at any single non-pinned hash. We sample one random hash per run.
static void check_subject_id_math(const uint32_t modulus)
{
    subject_id_fixture_t fixture;
    subject_id_fixture_init(&fixture, modulus);

    const uint64_t       hash         = random_non_pinned_hash(modulus);
    const uint32_t       eviction_max = modulus / 2U;
    const size_t         bitset_bytes = (((size_t)modulus) + 7U) / 8U;
    unsigned char* const seen_sid     = (unsigned char*)calloc(bitset_bytes, 1U);
    TEST_ASSERT_NOT_NULL(seen_sid);

    for (uint32_t evictions = 0U; evictions <= eviction_max; evictions++) {
        const uint32_t subject_id = topic_subject_id_impl(&fixture.cy, hash, evictions);
        if (subject_id <= CY_PINNED_SUBJECT_ID_MAX) {
            fail_check("pinned SID produced for non-pinned hash", modulus, hash, evictions, subject_id, 0U);
        }
        if (evictions < 10) {
            printf("hash=%llu evictions=%lu => subject_id=%lu\n",
                   (unsigned long long)hash,
                   (unsigned long)evictions,
                   (unsigned long)subject_id);
        }

        const uint32_t base = subject_id - SUBJECT_ID_OFFSET;
        if (base >= modulus) {
            fail_check("subject-ID out of modulus range", modulus, hash, evictions, subject_id, base);
        }
        if (bitset_get(seen_sid, base)) {
            fail_check("non-unique subject-ID within eviction bound", modulus, hash, evictions, subject_id, base);
        }
        bitset_set(seen_sid, base);

        const uint32_t recovered = topic_evictions_from_subject_id(hash, subject_id, modulus);
        if (recovered != evictions) {
            fail_check("eviction reconstruction mismatch", modulus, hash, evictions, subject_id, recovered);
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
