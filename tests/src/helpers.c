#include "helpers.h"
#include <rapidhash.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

void cy_test_serialize_u56(unsigned char out[7], uint64_t value)
{
    for (size_t i = 0; i < 7U; i++) {
        out[i] = (unsigned char)((value >> (i * 8U)) & 0xFFU);
    }
}

void cy_test_serialize_u64(unsigned char out[8], uint64_t value)
{
    for (size_t i = 0; i < 8U; i++) {
        out[i] = (unsigned char)((value >> (i * 8U)) & 0xFFU);
    }
}

uint64_t cy_test_deserialize_u56(const unsigned char in[7])
{
    uint64_t out = 0;
    for (size_t i = 0; i < 7U; i++) {
        out |= ((uint64_t)in[i]) << (i * 8U);
    }
    return out;
}

uint64_t cy_test_deserialize_u64(const unsigned char in[8])
{
    uint64_t out = 0;
    for (size_t i = 0; i < 8U; i++) {
        out |= ((uint64_t)in[i]) << (i * 8U);
    }
    return out;
}

void cy_test_make_message_header(unsigned char  out[16],
                                 const uint8_t  type,
                                 const uint64_t tag56,
                                 const uint64_t topic_hash)
{
    out[0] = (unsigned char)(type & 31U);
    cy_test_serialize_u56(&out[1], tag56);
    cy_test_serialize_u64(&out[8], topic_hash);
}

static uint64_t prng_next(uint64_t* const state)
{
    *state += 0xA0761D6478BD642FULL; // add Wyhash seed (64-bit prime)
    return rapidhash(state, sizeof(uint64_t));
}

static uint64_t get_prng_seed(void)
{
    const char* const env = getenv("PRNG_SEED");
    if (env != NULL) {
        return strtoull(env, NULL, 0);
    }
    const uint64_t seed = ((uint64_t)time(NULL) << 32U) ^ (uint64_t)clock();
    printf("PRNG_SEED=%llu\n", (unsigned long long)seed);
    return seed;
}

uint64_t prng(void)
{
    static uint64_t state  = 0;     // NOLINT(*-global-variables)
    static bool     seeded = false; // NOLINT(*-global-variables)
    if (!seeded) {
        state  = get_prng_seed();
        seeded = true;
    }
    return prng_next(&state);
}
