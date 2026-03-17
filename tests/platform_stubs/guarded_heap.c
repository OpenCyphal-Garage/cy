#include "guarded_heap.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Debug allocator model:
// - every allocation is wrapped with front/back canaries;
// - free() poisons payload and moves it into a bounded global quarantine;
// - actual release re-validates canaries + poison bytes to detect UAF writes deterministically.
typedef enum
{
    header_state_live = 1,
    header_state_quarantined
} header_state_t;

typedef struct header_t
{
    size_t           payload_size;
    guarded_heap_t*  owner;
    uint64_t         front_seed;
    uint64_t         back_seed;
    uint64_t         poison_seed;     // Seed used to fill/verify payload after free().
    struct header_t* quarantine_next; // Intrusive global FIFO link.
    header_state_t   state;
} header_t;

// Cross-heap quarantine is intentional: it preserves old blocks for longer and widens UAF detection windows.
static header_t* g_quarantine_head = NULL; // NOLINT(*-non-const-global-variables)
static header_t* g_quarantine_tail = NULL; // NOLINT(*-non-const-global-variables)
static size_t    g_quarantine_size = 0U;   // NOLINT(*-non-const-global-variables)

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

static void fill_random_from_state(unsigned char* const out, const size_t size, guarded_heap_t* const self)
{
    for (size_t i = 0U; i < size; i++) {
        out[i] = random_byte(&self->prng_state);
    }
}

static void fill_random_from_seed(unsigned char* const out, const size_t size, const uint64_t seed)
{
    uint64_t state = seed;
    for (size_t i = 0U; i < size; i++) {
        out[i] = random_byte(&state);
    }
}

static bool check_random_from_seed(const unsigned char* const in, const size_t size, const uint64_t seed)
{
    uint64_t state = seed;
    for (size_t i = 0U; i < size; i++) {
        if (in[i] != random_byte(&state)) {
            return false;
        }
    }
    return true;
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

static unsigned char* front_from_header(header_t* const header) { return (unsigned char*)(header + 1U); }

static const unsigned char* front_from_header_const(const header_t* const header)
{
    return (const unsigned char*)(header + 1U);
}

static unsigned char* payload_from_header(header_t* const header)
{
    return front_from_header(header) + GUARDED_HEAP_CANARY_SIZE;
}

static const unsigned char* payload_from_header_const(const header_t* const header)
{
    return front_from_header_const(header) + GUARDED_HEAP_CANARY_SIZE;
}

static unsigned char* back_from_header(header_t* const header)
{
    return payload_from_header(header) + header->payload_size;
}

static const unsigned char* back_from_header_const(const header_t* const header)
{
    return payload_from_header_const(header) + header->payload_size;
}

static void validate_fragment_live(const guarded_heap_t* const self, const header_t* const header)
{
    if (header->owner != self) {
        panic("wrong context");
    }
    if (header->state != header_state_live) {
        panic("invalid fragment state");
    }
    if (!check_canary(front_from_header_const(header), header->front_seed)) {
        panic("front canary mismatch");
    }
    if (!check_canary(back_from_header_const(header), header->back_seed)) {
        panic("back canary mismatch");
    }
}

static void validate_fragment_quarantined(const header_t* const header)
{
    if (header->state != header_state_quarantined) {
        panic("invalid quarantine state");
    }
    if (!check_canary(front_from_header_const(header), header->front_seed)) {
        panic("front canary mismatch");
    }
    if (!check_canary(back_from_header_const(header), header->back_seed)) {
        panic("back canary mismatch");
    }
    // Any payload mutation while quarantined indicates write-after-free.
    if (!check_random_from_seed(payload_from_header_const(header), header->payload_size, header->poison_seed)) {
        panic("use-after-free payload mutation");
    }
}

static void quarantine_release_fragment(header_t* const header)
{
    validate_fragment_quarantined(header);
    header->owner           = NULL;
    header->quarantine_next = NULL;
    free(header);
}

static void quarantine_release_oldest(void)
{
    header_t* const header = g_quarantine_head;
    if (header == NULL) {
        panic("quarantine underflow");
    }
    g_quarantine_head = header->quarantine_next;
    if (g_quarantine_head == NULL) {
        g_quarantine_tail = NULL;
    }
    header->quarantine_next = NULL;
    if (g_quarantine_size == 0U) {
        panic("quarantine size underflow");
    }
    g_quarantine_size--;
    quarantine_release_fragment(header);
}

static void quarantine_enqueue(header_t* const header)
{
    if (header == NULL) {
        panic("null quarantine header");
    }
    if (header->state != header_state_quarantined) {
        panic("enqueue state mismatch");
    }
    header->quarantine_next = NULL;
    if (g_quarantine_tail != NULL) {
        g_quarantine_tail->quarantine_next = header;
    } else {
        g_quarantine_head = header;
    }
    g_quarantine_tail = header;
    g_quarantine_size++;

    // Keep memory bounded while preserving a recent history of freed blocks.
    while (g_quarantine_size > GUARDED_HEAP_QUARANTINE_LIMIT) {
        quarantine_release_oldest();
    }
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
        panic("allocation byte counter overflow");
    }

    header->payload_size    = size;
    header->owner           = self;
    header->front_seed      = prng_next(&self->prng_state);
    header->back_seed       = prng_next(&self->prng_state);
    header->poison_seed     = 0U;
    header->quarantine_next = NULL;
    header->state           = header_state_live;

    fill_canary(front_from_header(header), header->front_seed);
    fill_canary(back_from_header(header), header->back_seed);
    fill_random_from_state(payload_from_header(header), size, self);

    self->allocated_fragments++;
    self->allocated_bytes += size;

    return payload_from_header(header);
}

static size_t fragment_size_checked(const guarded_heap_t* const self, const void* const payload)
{
    const header_t* const header = header_from_payload_const(payload);
    validate_fragment_live(self, header);
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
    validate_fragment_live(self, header);

    // Freeze the payload into a deterministic poison pattern for deferred UAF-write checks.
    header->poison_seed = prng_next(&self->prng_state);
    fill_random_from_seed(payload_from_header(header), header->payload_size, header->poison_seed);
    header->state = header_state_quarantined;

    if (self->allocated_fragments == 0U) {
        panic("fragment counter underflow");
    }
    if (self->allocated_bytes < header->payload_size) {
        panic("byte counter underflow");
    }
    self->allocated_fragments--;
    self->allocated_bytes -= header->payload_size;

    // Actual free happens later, after quarantine retention and re-validation.
    quarantine_enqueue(header);
}
