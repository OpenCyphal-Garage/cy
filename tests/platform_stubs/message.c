#include "message.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

typedef struct
{
    cy_message_t  base;
    size_t        skip_offset;
    size_t        payload_size;
    unsigned char payload[];
} test_message_t;

static size_t g_live_count    = 0;
static size_t g_destroy_count = 0;

static size_t smaller(const size_t a, const size_t b) { return (a < b) ? a : b; }

static void test_message_skip(cy_message_t* const msg, const size_t offset)
{
    test_message_t* const self = (test_message_t*)msg;
    assert(self->skip_offset <= self->payload_size);
    const size_t available = self->payload_size - self->skip_offset;
    self->skip_offset += smaller(offset, available);
}

static size_t test_message_read(const cy_message_t* const msg,
                                const size_t              offset,
                                const size_t              size,
                                void* const               output)
{
    const test_message_t* const self = (const test_message_t*)msg;
    if ((output == NULL) || (self->skip_offset > self->payload_size)) {
        return 0;
    }
    if (offset > (SIZE_MAX - self->skip_offset)) {
        return 0;
    }
    const size_t start = self->skip_offset + offset;
    if (start >= self->payload_size) {
        return 0;
    }
    const size_t count = smaller(size, self->payload_size - start);
    if (count > 0U) {
        memcpy(output, &self->payload[start], count);
    }
    return count;
}

static size_t test_message_size(const cy_message_t* const msg)
{
    const test_message_t* const self = (const test_message_t*)msg;
    assert(self->skip_offset <= self->payload_size);
    return self->payload_size - self->skip_offset;
}

static void test_message_destroy(cy_message_t* const msg)
{
    test_message_t* const self = (test_message_t*)msg;
    assert(g_live_count > 0U);
    g_live_count--;
    g_destroy_count++;
    self->base.vtable   = NULL;
    self->base.refcount = 0;
    self->skip_offset   = self->payload_size;
    free(self);
}

static const cy_message_vtable_t g_vtable = {
    .skip    = test_message_skip,
    .read    = test_message_read,
    .size    = test_message_size,
    .destroy = test_message_destroy,
};

cy_message_t* cy_test_message_make(const void* const data, const size_t size)
{
    if ((size > 0U) && (data == NULL)) {
        return NULL;
    }
    test_message_t* const self = (test_message_t*)malloc(sizeof(test_message_t) + size);
    if (self == NULL) {
        return NULL;
    }
    self->base.refcount = 1U;
    self->base.vtable   = &g_vtable;
    self->skip_offset   = 0U;
    self->payload_size  = size;
    if (size > 0U) {
        memcpy(self->payload, data, size);
    }
    g_live_count++;
    return &self->base;
}

size_t cy_test_message_live_count(void) { return g_live_count; }

size_t cy_test_message_destroy_count(void) { return g_destroy_count; }

void cy_test_message_reset_counters(void) { g_destroy_count = 0U; }
