#pragma once

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define GUARDED_HEAP_CANARY_SIZE 256UL

typedef struct
{
    size_t   allocated_fragments;
    size_t   allocated_bytes;
    uint64_t prng_state;
} guarded_heap_t;

void   guarded_heap_init(guarded_heap_t* self, uint64_t seed);
void   guarded_heap_reset(guarded_heap_t* self);
size_t guarded_heap_allocated_fragments(const guarded_heap_t* self);
size_t guarded_heap_allocated_bytes(const guarded_heap_t* self);

void* guarded_heap_alloc(void* context, size_t size);
void* guarded_heap_realloc(void* context, void* ptr, size_t size);
void  guarded_heap_free(void* context, void* ptr);

#ifdef __cplusplus
}
#endif
