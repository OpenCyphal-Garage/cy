#include "helpers.h"
#include <stdlib.h>

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

void* cy_test_realloc(void* const ptr, const size_t size)
{
    if (size == 0U) {
        free(ptr);
        return NULL;
    }
    return realloc(ptr, size);
}

void* cy_test_zalloc(const size_t size) { return calloc(1U, size); }

void cy_test_free(void* const ptr) { free(ptr); }
