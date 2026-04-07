#pragma once

#include <cy_can.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define CAN_TEST_MAX_IFACES    2U
#define CAN_TEST_MAX_NODES     4U
#define CAN_TEST_MAX_QUEUE     512U
#define CAN_TEST_MAX_TX_RECORD 1024U
#define CAN_TEST_MAX_FILTERS   64U
#define CAN_TEST_SKIP_CODE     77

typedef struct
{
    size_t allocated_fragments;
    size_t allocated_bytes;
    size_t allocation_attempts;
    size_t fail_after_n_allocations;
} can_test_heap_t;

typedef struct
{
    uint32_t      can_id;
    uint_least8_t iface_index;
    uint_least8_t len;
    bool          fd;
    uint8_t       data[64];
} can_test_tx_record_t;

typedef struct can_test_node_t can_test_node_t;

typedef struct
{
    can_test_node_t* nodes[CAN_TEST_MAX_NODES];
} can_test_bus_t;

struct can_test_node_t
{
    can_test_bus_t*      bus;
    can_test_heap_t      heap;
    cy_can_vtable_t      vtable;
    cy_platform_t*       platform;
    cy_t*                cy;
    cy_us_t              now;
    uint64_t             random_state;
    uint_least8_t        iface_count;
    bool                 fd_capable;
    bool                 self_loopback;
    bool                 drop_tx[CAN_TEST_MAX_IFACES];
    size_t               tx_blocked[CAN_TEST_MAX_IFACES];
    size_t               tx_classic_calls;
    size_t               tx_fd_calls;
    size_t               rx_calls;
    uint_least8_t        last_tx_pending_iface_bitmap;
    size_t               filter_calls;
    size_t               filter_failures_remaining;
    size_t               last_filter_count;
    canard_filter_t      last_filters[CAN_TEST_MAX_FILTERS];
    size_t               rx_head;
    size_t               rx_count;
    cy_can_rx_t          rx_queue[CAN_TEST_MAX_QUEUE];
    size_t               tx_history_count;
    can_test_tx_record_t tx_history[CAN_TEST_MAX_TX_RECORD];
};

void   can_test_heap_init(can_test_heap_t* self);
void   can_test_heap_fail_after(can_test_heap_t* self, size_t successful_allocations);
void   can_test_heap_allow_all(can_test_heap_t* self);
size_t can_test_heap_allocated_fragments(const can_test_heap_t* self);
size_t can_test_heap_allocated_bytes(const can_test_heap_t* self);
void*  can_test_heap_realloc(void* user, void* ptr, size_t size);

void can_test_bus_init(can_test_bus_t* self);

void can_test_node_prepare(can_test_node_t* self,
                           can_test_bus_t*  bus,
                           uint_least8_t    iface_count,
                           bool             fd_capable,
                           bool             enable_filter_callback);
void can_test_node_make_platform(can_test_node_t* self, size_t tx_queue_capacity, size_t filter_count);
void can_test_node_make_cy(can_test_node_t* self, const char* home);
void can_test_node_destroy(can_test_node_t* self);

void can_test_node_spin(can_test_node_t* self, cy_us_t slice);
void can_test_spin_pair(can_test_node_t* a, can_test_node_t* b, size_t rounds, cy_us_t slice);
bool can_test_spin_pair_until_future_done(can_test_node_t* a,
                                          can_test_node_t* b,
                                          cy_future_t*     future,
                                          size_t           rounds,
                                          cy_us_t          slice);
bool can_test_spin_pair_until_condition(can_test_node_t* a,
                                        can_test_node_t* b,
                                        bool (*condition)(void*),
                                        void*   context,
                                        size_t  rounds,
                                        cy_us_t slice);

void   can_test_node_reset_history(can_test_node_t* self);
size_t can_test_node_count_records_on_iface(const can_test_node_t* self, uint_least8_t iface_index);

size_t can_test_message_read_all(const cy_message_t* message, void* out, size_t capacity);
void   can_test_assert_message_equals(const cy_message_t* message, const void* expected, size_t size);
void   can_test_fill_payload(uint8_t* out, size_t size, uint8_t seed);

#ifdef __cplusplus
}
#endif
