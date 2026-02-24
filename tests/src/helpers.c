#include "helpers.h"
#include <rapidhash.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static void serialize_u64(unsigned char out[8], const uint64_t value)
{
    for (size_t i = 0U; i < 8U; i++) {
        out[i] = (unsigned char)((value >> (i * 8U)) & 0xFFU);
    }
}

static void serialize_u32(unsigned char out[4], const uint32_t value)
{
    for (size_t i = 0U; i < 4U; i++) {
        out[i] = (unsigned char)((value >> (i * 8U)) & 0xFFU);
    }
}

void make_message_header(unsigned char out[18], const uint8_t type, const uint64_t tag, const uint64_t topic_hash)
{
    out[0] = (unsigned char)(type & 63U);
    out[1] = 0U;
    serialize_u64(&out[2], tag);
    serialize_u64(&out[10], topic_hash);
}

size_t make_gossip_header(unsigned char* const out,
                          const size_t         out_size,
                          const uint8_t        ttl,
                          const int8_t         topic_log_age,
                          const uint64_t       topic_hash,
                          const uint32_t       topic_evictions,
                          const cy_str_t       topic_name)
{
    if ((out == NULL) || (topic_name.str == NULL) || (topic_name.len > CY_TOPIC_NAME_MAX)) {
        return 0U;
    }
    const size_t total_size = 18U + topic_name.len;
    if ((out_size < total_size) || (topic_name.len > UINT8_MAX)) {
        return 0U;
    }
    out[0] = 7U;
    out[1] = 0U;
    out[2] = ttl;
    out[3] = 0U;
    out[4] = (unsigned char)topic_log_age;
    serialize_u64(&out[5], topic_hash);
    serialize_u32(&out[13], topic_evictions);
    out[17] = (unsigned char)topic_name.len;
    if (topic_name.len > 0U) {
        memcpy(&out[18], topic_name.str, topic_name.len);
    }
    return total_size;
}

size_t make_scout_header(unsigned char* const out,
                         const size_t         out_size,
                         const uint64_t       incompatibility,
                         const cy_str_t       pattern)
{
    if ((out == NULL) || (pattern.str == NULL) || (pattern.len > CY_TOPIC_NAME_MAX)) {
        return 0U;
    }
    const size_t total_size = 18U + pattern.len;
    if ((out_size < total_size) || (pattern.len > UINT8_MAX)) {
        return 0U;
    }
    out[0] = 8U;
    memset(&out[1], 0, 8U);
    serialize_u64(&out[9], incompatibility);
    out[17] = (unsigned char)pattern.len;
    if (pattern.len > 0U) {
        memcpy(&out[18], pattern.str, pattern.len);
    }
    return total_size;
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
    printf("PRNG_SEED=%ju\n", (uintmax_t)seed);
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
