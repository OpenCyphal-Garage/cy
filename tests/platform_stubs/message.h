#pragma once

#include <cy_platform.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

cy_message_t* cy_test_message_make(const void* data, size_t size);

size_t cy_test_message_live_count(void);
size_t cy_test_message_destroy_count(void);
void   cy_test_message_reset_counters(void);

#ifdef __cplusplus
}
#endif
