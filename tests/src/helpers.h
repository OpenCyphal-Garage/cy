#pragma once

#include <cy_platform.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

void make_message_header(unsigned char out[24], uint8_t type, uint64_t tag, uint64_t topic_hash);

size_t make_gossip_header(unsigned char* out,
                          size_t         out_size,
                          uint8_t        ttl,
                          int8_t         topic_log_age,
                          uint64_t       topic_hash,
                          uint32_t       topic_evictions,
                          cy_str_t       topic_name);

size_t make_scout_header(unsigned char* out, size_t out_size, uint64_t incompatibility, cy_str_t pattern);

#ifdef __cplusplus
}
#endif
