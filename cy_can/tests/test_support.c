#include "test_support.h"
#include <cy_platform.h>
#include <unity.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct allocation_header_t
{
    size_t           size;
    uint32_t         magic;
    uint32_t         reserved;
    can_test_heap_t* owner;
} allocation_header_t;

static const uint32_t allocation_magic = UINT32_C(0xC0DEFACE);

static size_t smaller(const size_t a, const size_t b) { return (a < b) ? a : b; }

static void* heap_allocate(can_test_heap_t* self, const size_t size)
{
    if ((self->fail_after_n_allocations != SIZE_MAX) && (self->allocation_attempts >= self->fail_after_n_allocations)) {
        return NULL;
    }
    self->allocation_attempts++;

    allocation_header_t* const header = (allocation_header_t*)malloc(sizeof(allocation_header_t) + size);
    if (header == NULL) {
        return NULL;
    }
    header->size  = size;
    header->magic = allocation_magic;
    header->owner = self;
    self->allocated_fragments++;
    self->allocated_bytes += size;
    return (void*)(header + 1);
}

static allocation_header_t* header_from_payload(void* const ptr)
{
    return (allocation_header_t*)((uint8_t*)ptr - sizeof(allocation_header_t));
}

static const allocation_header_t* header_from_payload_const(const void* const ptr)
{
    return (const allocation_header_t*)((const uint8_t*)ptr - sizeof(allocation_header_t));
}

static void heap_free(can_test_heap_t* const self, void* const ptr)
{
    TEST_ASSERT_NOT_NULL(self);
    if (ptr != NULL) {
        allocation_header_t* const header = header_from_payload(ptr);
        TEST_ASSERT_EQUAL_UINT32(allocation_magic, header->magic);
        TEST_ASSERT_TRUE(header->owner == self);
        TEST_ASSERT_TRUE(self->allocated_fragments > 0U);
        TEST_ASSERT_TRUE(self->allocated_bytes >= header->size);
        self->allocated_fragments--;
        self->allocated_bytes -= header->size;
        header->magic = 0U;
        free(header);
    }
}

static void bus_register_node(can_test_bus_t* const bus, can_test_node_t* const node)
{
    if (bus == NULL) {
        return;
    }
    for (size_t i = 0U; i < CAN_TEST_MAX_NODES; i++) {
        if (bus->nodes[i] == NULL) {
            bus->nodes[i] = node;
            return;
        }
    }
    TEST_FAIL_MESSAGE("bus registry exhausted");
}

static void bus_unregister_node(can_test_bus_t* const bus, can_test_node_t* const node)
{
    if (bus == NULL) {
        return;
    }
    for (size_t i = 0U; i < CAN_TEST_MAX_NODES; i++) {
        if (bus->nodes[i] == node) {
            bus->nodes[i] = NULL;
            return;
        }
    }
}

static void enqueue_rx(can_test_node_t* const self, const cy_can_rx_t* const frame)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_NOT_NULL(frame);
    TEST_ASSERT_TRUE(self->rx_count < CAN_TEST_MAX_QUEUE);
    self->rx_queue[(self->rx_head + self->rx_count) % CAN_TEST_MAX_QUEUE] = *frame;
    self->rx_count++;
}

static bool dequeue_rx(can_test_node_t* const self, cy_can_rx_t* const out_frame)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_NOT_NULL(out_frame);
    if (self->rx_count == 0U) {
        return false;
    }
    *out_frame    = self->rx_queue[self->rx_head];
    self->rx_head = (self->rx_head + 1U) % CAN_TEST_MAX_QUEUE;
    self->rx_count--;
    return true;
}

static void record_tx(can_test_node_t* const self,
                      const uint_least8_t    iface_index,
                      const uint32_t         can_id,
                      const bool             fd,
                      const void* const      data,
                      const uint_least8_t    len)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_TRUE(self->tx_history_count < CAN_TEST_MAX_TX_RECORD);
    can_test_tx_record_t* const rec = &self->tx_history[self->tx_history_count++];
    rec->can_id                     = can_id;
    rec->iface_index                = iface_index;
    rec->len                        = len;
    rec->fd                         = fd;
    if (len > 0U) {
        (void)memcpy(rec->data, data, len);
    }
}

static void propagate_tx(can_test_node_t* const self,
                         const uint_least8_t    iface_index,
                         const uint32_t         can_id,
                         const bool             fd,
                         const void* const      data,
                         const uint_least8_t    len)
{
    if (self->bus == NULL) {
        return;
    }
    for (size_t i = 0U; i < CAN_TEST_MAX_NODES; i++) {
        can_test_node_t* const other = self->bus->nodes[i];
        if (other == NULL) {
            continue;
        }
        if ((other == self) && !self->self_loopback) {
            continue;
        }
        if (iface_index >= other->iface_count) {
            continue;
        }
        cy_can_rx_t frame;
        (void)memset(&frame, 0, sizeof(frame));
        frame.timestamp   = self->now;
        frame.can_id      = can_id;
        frame.iface_index = iface_index;
        frame.len         = len;
        frame.fd          = fd;
        if (len > 0U) {
            (void)memcpy(frame.data, data, len);
        }
        enqueue_rx(other, &frame);
    }
}

static bool tx_common(void* const         user,
                      const uint_least8_t iface_index,
                      const uint32_t      can_id,
                      const bool          fd,
                      const void* const   data,
                      const uint_least8_t len)
{
    can_test_node_t* const self = (can_test_node_t*)user;
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_TRUE(iface_index < self->iface_count);
    if (self->tx_blocked[iface_index] > 0U) {
        self->tx_blocked[iface_index]--;
        return false;
    }
    record_tx(self, iface_index, can_id, fd, data, len);
    if (!self->drop_tx[iface_index]) {
        propagate_tx(self, iface_index, can_id, fd, data, len);
    }
    return true;
}

static bool v_tx_classic(void* const         user,
                         const uint_least8_t iface_index,
                         const uint32_t      can_id,
                         const void* const   data,
                         const uint_least8_t len)
{
    can_test_node_t* const self = (can_test_node_t*)user;
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_TRUE(len <= 8U);
    self->tx_classic_calls++;
    return tx_common(user, iface_index, can_id, false, data, len);
}

static bool v_tx_fd(void* const         user,
                    const uint_least8_t iface_index,
                    const uint32_t      can_id,
                    const void* const   data,
                    const uint_least8_t len)
{
    can_test_node_t* const self = (can_test_node_t*)user;
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_TRUE(len <= 64U);
    self->tx_fd_calls++;
    return tx_common(user, iface_index, can_id, true, data, len);
}

static bool v_rx(void* const         user,
                 cy_can_rx_t* const  out_frame,
                 const cy_us_t       deadline,
                 const uint_least8_t tx_pending_iface_bitmap)
{
    can_test_node_t* const self = (can_test_node_t*)user;
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_NOT_NULL(out_frame);
    self->rx_calls++;
    self->last_tx_pending_iface_bitmap = tx_pending_iface_bitmap;
    if (dequeue_rx(self, out_frame)) {
        if (self->now < out_frame->timestamp) {
            self->now = out_frame->timestamp;
        }
        return true;
    }
    if (self->now <= deadline) {
        self->now = deadline + 1;
    }
    return false;
}

static bool v_filter(void* const user, const size_t filter_count, const canard_filter_t* const filters)
{
    can_test_node_t* const self = (can_test_node_t*)user;
    TEST_ASSERT_NOT_NULL(self);
    if ((filter_count > 0U) && (filters == NULL)) {
        return false;
    }
    self->filter_calls++;
    self->last_filter_count = filter_count;
    if (filter_count > 0U) {
        TEST_ASSERT_TRUE(filter_count <= CAN_TEST_MAX_FILTERS);
        (void)memcpy(self->last_filters, filters, filter_count * sizeof(canard_filter_t));
    }
    if (self->filter_failures_remaining > 0U) {
        self->filter_failures_remaining--;
        return false;
    }
    return true;
}

static cy_us_t v_now(void* const user)
{
    const can_test_node_t* const self = (const can_test_node_t*)user;
    TEST_ASSERT_NOT_NULL(self);
    return self->now;
}

static void* v_realloc(void* const user, void* const ptr, const size_t size)
{
    can_test_node_t* const self = (can_test_node_t*)user;
    TEST_ASSERT_NOT_NULL(self);
    return can_test_heap_realloc(&self->heap, ptr, size);
}

void can_test_heap_init(can_test_heap_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    (void)memset(self, 0, sizeof(*self));
    self->fail_after_n_allocations = SIZE_MAX;
}

void can_test_heap_fail_after(can_test_heap_t* const self, const size_t successful_allocations)
{
    TEST_ASSERT_NOT_NULL(self);
    self->allocation_attempts      = 0U;
    self->fail_after_n_allocations = successful_allocations;
}

void can_test_heap_allow_all(can_test_heap_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    self->allocation_attempts      = 0U;
    self->fail_after_n_allocations = SIZE_MAX;
}

size_t can_test_heap_allocated_fragments(const can_test_heap_t* const self)
{
    return (self != NULL) ? self->allocated_fragments : 0U;
}

size_t can_test_heap_allocated_bytes(const can_test_heap_t* const self)
{
    return (self != NULL) ? self->allocated_bytes : 0U;
}

void* can_test_heap_realloc(void* const user, void* const ptr, const size_t size)
{
    can_test_heap_t* const self = (can_test_heap_t*)user;
    TEST_ASSERT_NOT_NULL(self);
    if (size == 0U) {
        heap_free(self, ptr);
        return NULL;
    }
    if (ptr == NULL) {
        return heap_allocate(self, size);
    }

    const allocation_header_t* const old_header = header_from_payload_const(ptr);
    TEST_ASSERT_EQUAL_UINT32(allocation_magic, old_header->magic);
    TEST_ASSERT_TRUE(old_header->owner == self);
    void* const out = heap_allocate(self, size);
    if (out == NULL) {
        return NULL;
    }
    (void)memcpy(out, ptr, smaller(size, old_header->size));
    heap_free(self, ptr);
    return out;
}

void can_test_bus_init(can_test_bus_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    (void)memset(self, 0, sizeof(*self));
}

void can_test_node_prepare(can_test_node_t* const self,
                           can_test_bus_t* const  bus,
                           const uint_least8_t    iface_count,
                           const bool             fd_capable,
                           const bool             enable_filter_callback)
{
    size_t node_index = 0U;
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_TRUE((iface_count > 0U) && (iface_count <= CAN_TEST_MAX_IFACES));
    if (bus != NULL) {
        while ((node_index < CAN_TEST_MAX_NODES) && (bus->nodes[node_index] != NULL)) {
            node_index++;
        }
    }
    (void)memset(self, 0, sizeof(*self));
    self->bus         = bus;
    self->now         = 1000;
    self->prng_seed   = UINT64_C(0x123456789ABCDEF0) ^ (UINT64_C(0x9E3779B97F4A7C15) * (uint64_t)(node_index + 1U));
    self->iface_count = iface_count;
    self->fd_capable  = fd_capable;
    can_test_heap_init(&self->heap);
    self->vtable.tx_classic = v_tx_classic;
    self->vtable.tx_fd      = fd_capable ? v_tx_fd : NULL;
    self->vtable.rx         = v_rx;
    self->vtable.filter     = enable_filter_callback ? v_filter : NULL;
    self->vtable.now        = v_now;
    self->vtable.realloc    = v_realloc;
    bus_register_node(bus, self);
}

void can_test_node_make_platform(can_test_node_t* const self, const size_t tx_queue_capacity, const size_t filter_count)
{
    TEST_ASSERT_NOT_NULL(self);
    self->platform =
      cy_can_new(self->iface_count, tx_queue_capacity, filter_count, self->prng_seed, &self->vtable, self);
    TEST_ASSERT_NOT_NULL(self->platform);
}

void can_test_node_make_cy(can_test_node_t* const self, const char* const home)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_NOT_NULL(home);
    TEST_ASSERT_NOT_NULL(self->platform);
    self->cy = cy_new(self->platform, cy_str(home), (cy_str_t){ 0U, NULL });
    TEST_ASSERT_NOT_NULL(self->cy);
}

void can_test_node_destroy(can_test_node_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    if (self->cy != NULL) {
        cy_destroy(self->cy);
        self->cy = NULL;
    }
    if (self->platform != NULL) {
        cy_can_destroy(self->platform);
        self->platform = NULL;
    }
    bus_unregister_node(self->bus, self);
    TEST_ASSERT_EQUAL_size_t(0U, self->rx_count);
    TEST_ASSERT_EQUAL_size_t(0U, can_test_heap_allocated_fragments(&self->heap));
    TEST_ASSERT_EQUAL_size_t(0U, can_test_heap_allocated_bytes(&self->heap));
}

void can_test_node_spin(can_test_node_t* const self, const cy_us_t slice)
{
    TEST_ASSERT_NOT_NULL(self);
    TEST_ASSERT_NOT_NULL(self->cy);
    TEST_ASSERT_TRUE(slice >= 0);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(self->cy, cy_now(self->cy) + slice));
}

void can_test_spin_pair(can_test_node_t* const a, can_test_node_t* const b, const size_t rounds, const cy_us_t slice)
{
    for (size_t i = 0U; i < rounds; i++) {
        if (a != NULL) {
            can_test_node_spin(a, slice);
        }
        if (b != NULL) {
            can_test_node_spin(b, slice);
        }
    }
}

bool can_test_spin_pair_until_future_done(can_test_node_t* const a,
                                          can_test_node_t* const b,
                                          cy_future_t* const     future,
                                          const size_t           rounds,
                                          const cy_us_t          slice)
{
    TEST_ASSERT_NOT_NULL(future);
    for (size_t i = 0U; i < rounds; i++) {
        if (cy_future_done(future)) {
            return true;
        }
        can_test_spin_pair(a, b, 1U, slice);
    }
    return cy_future_done(future);
}

bool can_test_spin_pair_until_condition(can_test_node_t* const a,
                                        can_test_node_t* const b,
                                        bool (*const condition)(void*),
                                        void* const   context,
                                        const size_t  rounds,
                                        const cy_us_t slice)
{
    TEST_ASSERT_NOT_NULL(condition);
    for (size_t i = 0U; i < rounds; i++) {
        if (condition(context)) {
            return true;
        }
        can_test_spin_pair(a, b, 1U, slice);
    }
    return condition(context);
}

void can_test_node_reset_history(can_test_node_t* const self)
{
    TEST_ASSERT_NOT_NULL(self);
    self->tx_history_count             = 0U;
    self->tx_classic_calls             = 0U;
    self->tx_fd_calls                  = 0U;
    self->last_tx_pending_iface_bitmap = 0U;
}

size_t can_test_node_count_records_on_iface(const can_test_node_t* const self, const uint_least8_t iface_index)
{
    TEST_ASSERT_NOT_NULL(self);
    size_t out = 0U;
    for (size_t i = 0U; i < self->tx_history_count; i++) {
        if (self->tx_history[i].iface_index == iface_index) {
            out++;
        }
    }
    return out;
}

size_t can_test_message_read_all(const cy_message_t* const message, void* const out, const size_t capacity)
{
    TEST_ASSERT_NOT_NULL(message);
    TEST_ASSERT_NOT_NULL(out);
    const size_t size = cy_message_size(message);
    TEST_ASSERT_TRUE(size <= capacity);
    TEST_ASSERT_EQUAL_size_t(size, cy_message_read(message, 0U, size, out));
    return size;
}

void can_test_assert_message_equals(const cy_message_t* const message, const void* const expected, const size_t size)
{
    uint8_t buffer[512];
    TEST_ASSERT_TRUE(size <= sizeof(buffer));
    TEST_ASSERT_EQUAL_size_t(size, can_test_message_read_all(message, buffer, sizeof(buffer)));
    TEST_ASSERT_EQUAL_UINT8_ARRAY(expected, buffer, size);
}

void can_test_fill_payload(uint8_t* const out, const size_t size, const uint8_t seed)
{
    TEST_ASSERT_NOT_NULL(out);
    for (size_t i = 0U; i < size; i++) {
        out[i] = (uint8_t)(seed + (uint8_t)i);
    }
}
