#include "helpers.h"
#include <string.h>

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

enum
{
    TEST_HEADER_BYTES = 24U
};

void make_message_header(unsigned char out[24], const uint8_t type, const uint64_t tag, const uint64_t topic_hash)
{
    // Test helper wire header layout:
    // [0] type, [1] reserved, [2] incompatibility, [3] log-age,
    // [4..7] evictions, [8..15] topic hash, [16..23] tag.
    out[0] = (unsigned char)(type & 63U);
    out[1] = 0U;
    out[2] = 0U;
    out[3] = 0U;
    serialize_u32(&out[4], 0U);
    serialize_u64(&out[8], topic_hash);
    serialize_u64(&out[16], tag);
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
    const size_t total_size = TEST_HEADER_BYTES + topic_name.len;
    if ((out_size < total_size) || (topic_name.len > UINT8_MAX)) {
        return 0U;
    }
    // Test helper gossip header layout:
    // [0] type, [2] ttl, [3] log-age, [8..15] topic hash, [16..19] evictions, [23] name length.
    out[0] = 8U;
    out[1] = 0U;
    out[2] = ttl;
    out[3] = (unsigned char)topic_log_age;
    memset(&out[4], 0, TEST_HEADER_BYTES - 4U);
    serialize_u64(&out[8], topic_hash);
    serialize_u32(&out[16], topic_evictions);
    out[TEST_HEADER_BYTES - 1U] = (unsigned char)topic_name.len;
    if (topic_name.len > 0U) {
        memcpy(&out[TEST_HEADER_BYTES], topic_name.str, topic_name.len);
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
    const size_t total_size = TEST_HEADER_BYTES + pattern.len;
    if ((out_size < total_size) || (pattern.len > UINT8_MAX)) {
        return 0U;
    }
    // Test helper scout header layout:
    // [0] type, [23] pattern length.
    out[0] = 9U;
    memset(&out[1], 0, TEST_HEADER_BYTES - 1U);
    serialize_u64(&out[8], incompatibility);
    out[TEST_HEADER_BYTES - 1U] = (unsigned char)pattern.len;
    if (pattern.len > 0U) {
        memcpy(&out[TEST_HEADER_BYTES], pattern.str, pattern.len);
    }
    return total_size;
}
