#include "guarded_heap.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct
{
    size_t          payload_size;
    guarded_heap_t* owner;
    uint64_t        front_seed;
    uint64_t        back_seed;
} header_t;

static void panic(const char* const message)
{
    (void)fprintf(stderr, "%s:%d: guarded heap panic: %s\n", __FILE__, __LINE__, message);
    (void)fflush(stderr);
    abort();
}

static guarded_heap_t* from_context(void* const context)
{
    guarded_heap_t* const out = (guarded_heap_t*)context;
    if (out == NULL) {
        panic("null context");
    }
    return out;
}

static uint64_t prng_next(uint64_t* const state)
{
    *state += UINT64_C(0x9E3779B97F4A7C15);
    uint64_t z = *state;
    z ^= z >> 30U;
    z *= UINT64_C(0xBF58476D1CE4E5B9);
    z ^= z >> 27U;
    z *= UINT64_C(0x94D049BB133111EB);
    z ^= z >> 31U;
    return z;
}

static unsigned char random_byte(uint64_t* const state)
{
    const uint64_t value = prng_next(state);
    return (unsigned char)(value >> 56U);
}

static void fill_canary(unsigned char* const out, const uint64_t seed)
{
    uint64_t state = seed;
    for (size_t i = 0U; i < GUARDED_HEAP_CANARY_SIZE; i++) {
        out[i] = random_byte(&state);
    }
}

static bool check_canary(const unsigned char* const in, const uint64_t seed)
{
    uint64_t state = seed;
    for (size_t i = 0U; i < GUARDED_HEAP_CANARY_SIZE; i++) {
        if (in[i] != random_byte(&state)) {
            return false;
        }
    }
    return true;
}

static void random_fill(unsigned char* const out, const size_t size, guarded_heap_t* const self)
{
    for (size_t i = 0U; i < size; i++) {
        out[i] = random_byte(&self->prng_state);
    }
}

static bool allocation_total_size(const size_t payload_size, size_t* const out)
{
    const size_t overhead = sizeof(header_t) + (GUARDED_HEAP_CANARY_SIZE * 2U);
    if (payload_size > (SIZE_MAX - overhead)) {
        return false;
    }
    *out = overhead + payload_size;
    return true;
}

static header_t* header_from_payload(void* const payload)
{
    const unsigned char* const raw = (unsigned char*)payload;
    return (header_t*)(raw - GUARDED_HEAP_CANARY_SIZE - sizeof(header_t));
}

static const header_t* header_from_payload_const(const void* const payload)
{
    const unsigned char* const raw = (const unsigned char*)payload;
    return (const header_t*)(raw - GUARDED_HEAP_CANARY_SIZE - sizeof(header_t));
}

static void* allocate_fragment(guarded_heap_t* const self, const size_t size)
{
    if (size == 0U) {
        return NULL;
    }

    size_t total_size = 0U;
    if (!allocation_total_size(size, &total_size)) {
        return NULL;
    }

    header_t* const header = (header_t*)malloc(total_size);
    if (header == NULL) {
        return NULL;
    }

    if (self->allocated_bytes > (SIZE_MAX - size)) {
        free(header);
        panic("allocation byte counter overflow");
    }

    header->payload_size = size;
    header->owner        = self;
    header->front_seed   = prng_next(&self->prng_state);
    header->back_seed    = prng_next(&self->prng_state);

    unsigned char* const front   = (unsigned char*)(header + 1U);
    unsigned char* const payload = front + GUARDED_HEAP_CANARY_SIZE;
    unsigned char* const back    = payload + size;
    fill_canary(front, header->front_seed);
    fill_canary(back, header->back_seed);
    random_fill(payload, size, self);

    self->allocated_fragments++;
    self->allocated_bytes += size;

    return payload;
}

static size_t fragment_size_checked(const guarded_heap_t* const self, const void* const payload)
{
    const header_t* const header = header_from_payload_const(payload);
    if (header->owner != self) {
        panic("wrong context");
    }
    const unsigned char* const front = (const unsigned char*)(header + 1U);
    const unsigned char* const back  = front + GUARDED_HEAP_CANARY_SIZE + header->payload_size;

    if (!check_canary(front, header->front_seed)) {
        panic("front canary mismatch");
    }
    if (!check_canary(back, header->back_seed)) {
        panic("back canary mismatch");
    }
    return header->payload_size;
}

void guarded_heap_init(guarded_heap_t* const self, const uint64_t seed)
{
    if (self == NULL) {
        panic("null heap");
    }
    self->allocated_fragments = 0U;
    self->allocated_bytes     = 0U;
    self->prng_state          = (seed != 0U) ? seed : UINT64_C(0xA0761D6478BD642F);
}

void guarded_heap_reset(guarded_heap_t* const self)
{
    if (self == NULL) {
        panic("null heap");
    }
    if (self->allocated_fragments != 0U) {
        panic("reset with outstanding fragments");
    }
    if (self->allocated_bytes != 0U) {
        panic("reset with outstanding bytes");
    }
    self->prng_state ^= prng_next(&self->prng_state);
}

size_t guarded_heap_allocated_fragments(const guarded_heap_t* const self)
{
    return (self != NULL) ? self->allocated_fragments : 0U;
}

size_t guarded_heap_allocated_bytes(const guarded_heap_t* const self)
{
    return (self != NULL) ? self->allocated_bytes : 0U;
}

void* guarded_heap_alloc(void* const context, const size_t size)
{
    guarded_heap_t* const self = from_context(context);
    return allocate_fragment(self, size);
}

void* guarded_heap_realloc(void* const context, void* const ptr, const size_t size)
{
    guarded_heap_t* const self = from_context(context);

    if (size == 0U) {
        guarded_heap_free(context, ptr);
        return NULL;
    }
    if (ptr == NULL) {
        return allocate_fragment(self, size);
    }

    const size_t old_size = fragment_size_checked(self, ptr);
    void* const  out      = allocate_fragment(self, size);
    if (out == NULL) {
        return NULL;
    }
    const size_t copy_size = (size < old_size) ? size : old_size;
    if (copy_size > 0U) {
        memcpy(out, ptr, copy_size);
    }
    guarded_heap_free(context, ptr);
    return out;
}

void guarded_heap_free(void* const context, void* const ptr)
{
    if (ptr == NULL) {
        return;
    }
    guarded_heap_t* const self   = from_context(context);
    header_t* const       header = header_from_payload(ptr);
    if (header->owner != self) {
        panic("wrong context");
    }
    unsigned char* const       front   = (unsigned char*)(header + 1U);
    unsigned char* const       payload = front + GUARDED_HEAP_CANARY_SIZE;
    const unsigned char* const back    = payload + header->payload_size;

    if (!check_canary(front, header->front_seed)) {
        panic("front canary mismatch");
    }
    if (!check_canary(back, header->back_seed)) {
        panic("back canary mismatch");
    }

    random_fill(payload, header->payload_size, self);

    if (self->allocated_fragments == 0U) {
        panic("fragment counter underflow");
    }
    if (self->allocated_bytes < header->payload_size) {
        panic("byte counter underflow");
    }
    self->allocated_fragments--;
    self->allocated_bytes -= header->payload_size;

    free(header);
}
