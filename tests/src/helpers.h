#pragma once

#include <cy_platform.h>
#include <stddef.h>
#include <stdint.h>
#include "guarded_heap.h"

#ifdef __cplusplus
extern "C"
{
#endif

void     cy_test_serialize_u56(unsigned char out[7], uint64_t value);
void     cy_test_serialize_u64(unsigned char out[8], uint64_t value);
uint64_t cy_test_deserialize_u56(const unsigned char in[7]);
uint64_t cy_test_deserialize_u64(const unsigned char in[8]);
void     cy_test_make_message_header(unsigned char out[16], uint8_t type, uint64_t tag56, uint64_t topic_hash);

/// A default trace sink for tests when CY_CONFIG_TRACE is enabled.
void cy_trace(cy_t* const         cy,
              const char* const   file,
              const uint_fast16_t line,
              const char* const   func,
              const char* const   format,
              ...);

#ifdef __cplusplus
}
#endif
