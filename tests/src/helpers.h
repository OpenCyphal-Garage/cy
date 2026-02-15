#pragma once

#include <cy_platform.h>
#include <stddef.h>
#include <stdint.h>
#include "guarded_heap.h"

#ifdef __cplusplus
extern "C"
{
#endif

void cy_test_make_message_header(unsigned char out[18], uint8_t type, uint64_t tag, uint64_t topic_hash);

/// The PRNG is seeded from the current time by default. If PRNG_SEED environment variable is set,
/// it is used as the seed instead of the current time to make the sequence deterministic.
uint64_t prng(void);

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
