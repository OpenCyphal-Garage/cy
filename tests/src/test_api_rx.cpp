#include <cy_platform.h>
#include <unity.h>
#include "api_mock_platform_utils.hpp"
#include "helpers.h"
#include "guarded_heap.h"
#include "message.h"
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>

namespace {
constexpr std::uint8_t header_msg_best_effort = 0U;
constexpr std::uint8_t header_msg_reliable    = 1U;
constexpr std::uint8_t header_msg_ack         = 2U;
constexpr std::size_t  header_bytes           = 24U;

struct arrival_capture_t
{
    std::size_t                   count{ 0U };
    std::array<std::uint64_t, 16> tags{};
    std::array<unsigned char, 16> first_payload_byte{};
};

struct self_unsub_capture_t
{
    std::size_t count{ 0U };
};

struct test_platform_t final
{
    cy_platform_t        platform{};
    cy_platform_vtable_t vtable{};
    guarded_heap_t       core_heap{};
    guarded_heap_t       message_heap{};

    cy_t* cy{ nullptr };

    cy_us_t       now{ 0 };
    std::uint64_t random_state{ 1U };

    std::size_t                   unicast_count{ 0U };
    std::array<unsigned char, 16> last_unicast{};
    std::size_t                   unicast_extent{ 0U };
};

test_platform_t* platform_from(cy_platform_t* const platform)
{
    return api_test::platform_from<test_platform_t>(platform);
}

extern "C" cy_subject_writer_t* platform_subject_writer_new(cy_platform_t* const platform,
                                                            const std::uint32_t  subject_id)
{
    return api_test::subject_writer_new<test_platform_t>(platform, subject_id);
}

extern "C" void platform_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    api_test::subject_writer_destroy<test_platform_t>(platform, writer);
}

extern "C" cy_err_t platform_subject_writer_send(cy_platform_t* const       platform,
                                                 cy_subject_writer_t* const writer,
                                                 const cy_us_t              deadline,
                                                 const cy_prio_t            priority,
                                                 const cy_bytes_t           message)
{
    (void)platform;
    (void)writer;
    (void)deadline;
    (void)priority;
    (void)message;
    return CY_OK;
}

extern "C" cy_subject_reader_t* platform_subject_reader_new(cy_platform_t* const platform,
                                                            const std::uint32_t  subject_id,
                                                            const std::size_t    extent)
{
    return api_test::subject_reader_new<test_platform_t>(platform, subject_id, extent);
}

extern "C" void platform_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    api_test::subject_reader_destroy<test_platform_t>(platform, reader);
}

extern "C" cy_err_t platform_unicast_send(cy_platform_t* const   platform,
                                          const cy_lane_t* const lane,
                                          const cy_us_t          deadline,
                                          const cy_bytes_t       message)
{
    (void)lane;
    (void)deadline;

    test_platform_t* const self = platform_from(platform);
    self->unicast_count++;
    self->last_unicast.fill(0U);

    std::size_t copied = 0U;
    for (const cy_bytes_t* frag = &message; (frag != nullptr) && (copied < self->last_unicast.size());
         frag                   = frag->next) {
        if ((frag->size == 0U) || (frag->data == nullptr)) {
            continue;
        }
        const std::size_t to_copy =
          ((self->last_unicast.size() - copied) < frag->size) ? (self->last_unicast.size() - copied) : frag->size;
        std::memcpy(self->last_unicast.data() + copied, frag->data, to_copy);
        copied += to_copy;
    }
    return CY_OK;
}

extern "C" void platform_unicast_extent_set(cy_platform_t* const platform, const std::size_t extent)
{
    platform_from(platform)->unicast_extent = extent;
}

extern "C" cy_err_t platform_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    (void)platform;
    (void)deadline;
    return CY_OK;
}

extern "C" cy_us_t platform_now(cy_platform_t* const platform) { return platform_from(platform)->now; }

extern "C" void* platform_realloc(cy_platform_t* const platform, void* const ptr, const std::size_t size)
{
    return api_test::core_heap_realloc<test_platform_t>(platform, ptr, size);
}

extern "C" std::uint64_t platform_random(cy_platform_t* const platform)
{
    return api_test::random_lcg<test_platform_t>(platform);
}

extern "C" void platform_on_async_error(cy_t* const         cy,
                                        cy_topic_t* const   topic,
                                        const cy_err_t      error,
                                        const std::uint16_t line_number)
{
    (void)cy;
    (void)topic;
    (void)error;       // Reported separately by the failing assertion below.
    (void)line_number; // Reported separately by the failing assertion below.
    TEST_FAIL_MESSAGE("Unexpected async error callback invocation");
}

extern "C" void on_arrival_capture(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }

    arrival_capture_t* const cap = static_cast<arrival_capture_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(cap);
    TEST_ASSERT(cap->count < cap->tags.size());
    const std::size_t idx = cap->count++;
    cap->tags.at(idx)     = arrival.breadcrumb.message_tag;

    unsigned char first = 0xFFU;
    if (cy_message_read(arrival.message.content, 0U, 1U, &first) == 0U) {
        first = 0xFFU;
    }
    cap->first_payload_byte.at(idx) = first;
    cy_message_refcount_dec(arrival.message.content);
}

extern "C" void on_arrival_self_unsub(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }

    self_unsub_capture_t* const cap = static_cast<self_unsub_capture_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(cap);
    cap->count++;
    cy_message_refcount_dec(arrival.message.content);
    cy_future_destroy(sub);
}

extern "C" void on_arrival_count_only(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == nullptr) {
        return;
    }

    self_unsub_capture_t* const cap = static_cast<self_unsub_capture_t*>(cy_future_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(cap);
    cap->count++;
    cy_message_refcount_dec(arrival.message.content);
}

void platform_init(test_platform_t* const self)
{
    *self = test_platform_t{};

    guarded_heap_init(&self->core_heap, UINT64_C(0xFACEB00C12345678));
    guarded_heap_init(&self->message_heap, UINT64_C(0xDEC0DE1234567890));

    self->vtable.subject_writer_new     = platform_subject_writer_new;
    self->vtable.subject_writer_destroy = platform_subject_writer_destroy;
    self->vtable.subject_writer_send    = platform_subject_writer_send;

    self->vtable.subject_reader_new     = platform_subject_reader_new;
    self->vtable.subject_reader_destroy = platform_subject_reader_destroy;

    self->vtable.unicast            = platform_unicast_send;
    self->vtable.unicast_extent_set = platform_unicast_extent_set;

    self->vtable.spin    = platform_spin;
    self->vtable.now     = platform_now;
    self->vtable.realloc = platform_realloc;
    self->vtable.random  = platform_random;

    api_test::init_platform_base(self->platform, self->vtable);

    self->cy = cy_new(&self->platform);
    TEST_ASSERT_NOT_NULL(self->cy);
    cy_async_error_handler_set(self->cy, platform_on_async_error);
}

void platform_deinit(test_platform_t* const self)
{
    if (self->cy != nullptr) {
        cy_destroy(self->cy);
        self->cy = nullptr;
    }
    api_test::assert_heaps_clean(self->core_heap, self->message_heap);
}

void assert_message_counters(const std::size_t destroyed, const std::size_t live)
{
    TEST_ASSERT_EQUAL_size_t(destroyed, cy_test_message_destroy_count());
    TEST_ASSERT_EQUAL_size_t(live, cy_test_message_live_count());
}

void dispatch_message(test_platform_t* const  self,
                      const cy_topic_t* const topic,
                      const std::uint8_t      type,
                      const std::uint64_t     tag,
                      const std::uint64_t     remote_id,
                      const cy_us_t           timestamp,
                      const unsigned char     payload_byte)
{
    std::array<unsigned char, header_bytes + 1U> wire{};
    make_message_header(wire.data(), type, tag, cy_topic_hash(topic));
    wire[header_bytes]       = payload_byte;
    const cy_lane_t     lane = { .id = remote_id, .ctx = { { 0 } }, .prio = cy_prio_nominal };
    cy_message_t* const msg  = cy_test_message_make(&self->message_heap, wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t message{};
    message.timestamp = timestamp;
    message.content   = msg;
    cy_on_message(&self->platform, lane, nullptr, message);
}

void dispatch_raw(test_platform_t* const     self,
                  const unsigned char* const wire,
                  const std::size_t          wire_size,
                  const cy_lane_t            lane,
                  const cy_subject_reader_t* reader,
                  const cy_us_t              timestamp)
{
    cy_message_t* const msg = cy_test_message_make(&self->message_heap, wire, wire_size);
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t message{};
    message.timestamp                     = timestamp;
    message.content                       = msg;
    const std::uint32_t* const subject_id = (reader != nullptr) ? &reader->subject_id : nullptr;
    cy_on_message(&self->platform, lane, subject_id, message);
}

std::uint32_t compute_subject_id(const std::uint64_t hash, const std::uint32_t evictions, const std::uint32_t modulus)
{
    const std::uint64_t offset =
      (hash + (static_cast<std::uint64_t>(evictions) * static_cast<std::uint64_t>(evictions))) % modulus;
    return CY_SUBJECT_ID_PINNED_MAX + 1U + static_cast<std::uint32_t>(offset);
}

void test_api_malformed_header_drops_message()
{
    test_platform_t platform{};
    platform_init(&platform);

    const std::array<unsigned char, 3> wire = { 0x01U, 0x02U, 0x03U };
    cy_message_t* const                msg  = cy_test_message_make(&platform.message_heap, wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t mts{};
    mts.timestamp        = 10;
    mts.content          = msg;
    const cy_lane_t lane = { .id = 1234U, .ctx = { { 0 } }, .prio = cy_prio_nominal };

    cy_on_message(&platform.platform, lane, nullptr, mts);
    TEST_ASSERT_EQUAL_size_t(1, cy_test_message_destroy_count());
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());
    TEST_ASSERT_EQUAL_size_t(0, platform.unicast_count);

    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_inline_msg_rejects_nonzero_incompatibility()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    self_unsub_capture_t capture{};
    cy_future_t* const   sub = cy_subscribe(platform.cy, cy_str("rx/inline/incompat"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_count_only);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/inline/incompat"));
    TEST_ASSERT_NOT_NULL(topic);
    std::array<unsigned char, header_bytes + 1U> wire{};
    make_message_header(wire.data(), header_msg_best_effort, UINT64_C(101), cy_topic_hash(topic));
    wire[2]              = 1U; // incompatibility
    wire[header_bytes]   = 0x11U;
    const cy_lane_t lane = { .id = UINT64_C(0x901), .ctx = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_raw(&platform, wire.data(), wire.size(), lane, nullptr, 200);
    TEST_ASSERT_EQUAL_size_t(0U, capture.count);
    TEST_ASSERT_EQUAL_size_t(0U, platform.unicast_count);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_inline_msg_rejects_invalid_lage()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    self_unsub_capture_t capture{};
    cy_future_t* const   sub = cy_subscribe(platform.cy, cy_str("rx/inline/lage"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_count_only);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/inline/lage"));
    TEST_ASSERT_NOT_NULL(topic);
    std::array<unsigned char, header_bytes + 1U> wire{};
    make_message_header(wire.data(), header_msg_best_effort, UINT64_C(106), cy_topic_hash(topic));
    wire[3]              = static_cast<unsigned char>(127); // invalid lage (> LAGE_MAX)
    wire[header_bytes]   = 0x66U;
    const cy_lane_t lane = { .id = UINT64_C(0x906), .ctx = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_raw(&platform, wire.data(), wire.size(), lane, nullptr, 205);
    TEST_ASSERT_EQUAL_size_t(0U, capture.count);
    TEST_ASSERT_EQUAL_size_t(0U, platform.unicast_count);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_inline_msg_rejects_pinned_evictions_lage_mismatch()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    self_unsub_capture_t capture{};
    cy_future_t* const   sub = cy_subscribe(platform.cy, cy_str("#0005"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_count_only);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("#0005"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_TRUE(cy_topic_hash(topic) == 0x0005U); // Bare pin: hash equals pin value.

    // Send a message with pinned evictions but non-pinned lage (mismatch should be rejected).
    std::array<unsigned char, header_bytes + 1U> wire{};
    make_message_header(wire.data(), header_msg_best_effort, UINT64_C(102), cy_topic_hash(topic));
    // Set pinned evictions (UINT32_MAX - 5 = pin to subject 5) in little-endian.
    const auto pinned_ev = static_cast<std::uint32_t>(UINT32_MAX - 5U);
    wire[4]              = static_cast<unsigned char>(pinned_ev >> 0U);
    wire[5]              = static_cast<unsigned char>(pinned_ev >> 8U);
    wire[6]              = static_cast<unsigned char>(pinned_ev >> 16U);
    wire[7]              = static_cast<unsigned char>(pinned_ev >> 24U);
    // lage remains 0 (non-pinned), creating the mismatch.
    wire[header_bytes]   = 0x22U;
    const cy_lane_t lane = { .id = UINT64_C(0x902), .ctx = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_raw(&platform, wire.data(), wire.size(), lane, nullptr, 201);
    TEST_ASSERT_EQUAL_size_t(0U, capture.count);
    TEST_ASSERT_EQUAL_size_t(0U, platform.unicast_count);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_inline_msg_rejects_multicast_subject_mismatch()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    self_unsub_capture_t capture{};
    cy_future_t* const   sub = cy_subscribe(platform.cy, cy_str("rx/inline/mismatch"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_count_only);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/inline/mismatch"));
    TEST_ASSERT_NOT_NULL(topic);
    const std::uint64_t       hash     = cy_topic_hash(topic);
    const std::uint32_t       modulus  = platform.platform.subject_id_modulus;
    const std::uint32_t       expected = compute_subject_id(hash, 0U, modulus);
    const std::uint32_t       max_sid  = CY_SUBJECT_ID_MAX(modulus);
    const std::uint32_t       mismatch = (expected < max_sid) ? (expected + 1U) : (expected - 1U);
    const cy_subject_reader_t reader   = { .subject_id = mismatch, .extent = 0 };

    std::array<unsigned char, header_bytes + 1U> wire{};
    make_message_header(wire.data(), header_msg_best_effort, UINT64_C(103), hash);
    wire[header_bytes]   = 0x33U;
    const cy_lane_t lane = { .id = UINT64_C(0x903), .ctx = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_raw(&platform, wire.data(), wire.size(), lane, &reader, 202);
    TEST_ASSERT_EQUAL_size_t(0U, capture.count);
    TEST_ASSERT_EQUAL_size_t(0U, platform.unicast_count);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_inline_msg_unicast_skips_subject_consistency_check()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    arrival_capture_t  capture{};
    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/inline/unicast/consistency"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_capture);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/inline/unicast/consistency"));
    TEST_ASSERT_NOT_NULL(topic);
    std::array<unsigned char, header_bytes + 1U> wire{};
    make_message_header(wire.data(), header_msg_best_effort, UINT64_C(104), cy_topic_hash(topic));
    wire[4]              = 1U; // mismatched evictions would alter multicast subject mapping
    wire[header_bytes]   = 0x44U;
    const cy_lane_t lane = { .id = UINT64_C(0x904), .ctx = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_raw(&platform, wire.data(), wire.size(), lane, nullptr, 203);
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(104), capture.tags[0]);
    TEST_ASSERT_EQUAL_size_t(0U, platform.unicast_count);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_inline_msg_unknown_topic_collision_path_smoke()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    self_unsub_capture_t capture{};
    cy_future_t* const   sub = cy_subscribe(platform.cy, cy_str("rx/inline/collision/local"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_count_only);

    const cy_topic_t* const local_topic = cy_topic_find_by_name(platform.cy, cy_str("rx/inline/collision/local"));
    TEST_ASSERT_NOT_NULL(local_topic);
    const std::uint32_t modulus     = platform.platform.subject_id_modulus;
    const std::uint64_t remote_hash = cy_topic_hash(local_topic) + static_cast<std::uint64_t>(modulus);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(platform.cy, remote_hash));
    const cy_subject_reader_t reader = { .subject_id = compute_subject_id(remote_hash, 0U, modulus), .extent = 0 };

    std::array<unsigned char, header_bytes + 1U> wire{};
    make_message_header(wire.data(), header_msg_best_effort, UINT64_C(105), remote_hash);
    wire[header_bytes]   = 0x55U;
    const cy_lane_t lane = { .id = UINT64_C(0x905), .ctx = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_raw(&platform, wire.data(), wire.size(), lane, &reader, 204);
    TEST_ASSERT_EQUAL_size_t(0U, capture.count);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_reliable_duplicate_acked_once_to_application()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    arrival_capture_t  capture{};
    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/dup"), 256U);
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_capture);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/dup"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_reliable, 0x1234U, 0xAAU, 100, 0x11U);
    dispatch_message(&platform, topic, header_msg_reliable, 0x1234U, 0xAAU, 101, 0x22U);

    TEST_ASSERT_EQUAL_size_t(1, capture.count);
    TEST_ASSERT_EQUAL_UINT64(0x1234U, capture.tags[0]);
    TEST_ASSERT_EQUAL_size_t(2, platform.unicast_count);
    TEST_ASSERT_EQUAL_UINT8(header_msg_ack, static_cast<std::uint8_t>(platform.last_unicast[0] & 63U));
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));

    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_ordered_subscriber_timeout_flush()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    arrival_capture_t  capture{};
    cy_future_t* const sub = cy_subscribe_ordered(platform.cy, cy_str("rx/ord"), 256U, 10);
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_capture);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/ord"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_best_effort, 8U, 0xBBU, 100, 0x41U);
    dispatch_message(&platform, topic, header_msg_best_effort, 9U, 0xBBU, 101, 0x42U);
    TEST_ASSERT_EQUAL_size_t(0, capture.count);
    TEST_ASSERT_EQUAL_size_t(0, platform.unicast_count);

    platform.now = 1000;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_EQUAL_size_t(2, capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, capture.tags[0]);
    TEST_ASSERT_EQUAL_UINT64(9U, capture.tags[1]);
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));

    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_unsubscribe_from_own_callback_is_deferred_and_safe()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    self_unsub_capture_t capture{};
    cy_future_t* const   sub = cy_subscribe(platform.cy, cy_str("rx/unsub/self"), 256U);
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_self_unsub);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/unsub/self"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_best_effort, 100U, 0xA1U, 100, 0x11U);
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);

    // Deferred destruction executes from the event loop.
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));

    // After deferred destruction, the callback shall no longer be invoked.
    dispatch_message(&platform, topic, header_msg_best_effort, 101U, 0xA1U, 101, 0x22U);
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());

    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_unsubscribe_effect_is_applied_on_spin()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    self_unsub_capture_t capture{};
    cy_future_t* const   sub = cy_subscribe(platform.cy, cy_str("rx/unsub/deferred"), 256U);
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_future_context_set(sub, context);
    cy_future_callback_set(sub, on_arrival_count_only);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/unsub/deferred"));
    TEST_ASSERT_NOT_NULL(topic);

    cy_future_destroy(sub);

    // Destruction is deferred, but callbacks are disabled immediately.
    dispatch_message(&platform, topic, header_msg_best_effort, 200U, 0xA2U, 100, 0x31U);
    TEST_ASSERT_EQUAL_size_t(0U, capture.count);

    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));

    dispatch_message(&platform, topic, header_msg_best_effort, 201U, 0xA2U, 101, 0x32U);
    TEST_ASSERT_EQUAL_size_t(0U, capture.count);
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());

    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_subscriber_destroy_releases_pending_arrival_without_double_free()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/subscriber/dispose"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/subscriber/dispose"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_best_effort, UINT64_C(0x4A1), UINT64_C(0xAB), 150, 0x5AU);
    assert_message_counters(0U, 1U);

    cy_future_destroy(sub); // Releases retained arrival in subscriber_dispose().
    assert_message_counters(1U, 0U);

    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy)); // Runs subscriber_destroy(); must not destroy again.
    assert_message_counters(1U, 0U);

    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_subscriber_move_demotes_done_unless_liveness()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/subscriber/move"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/subscriber/move"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_best_effort, UINT64_C(0x501), UINT64_C(0xD1), 100, 0xA1U);
    TEST_ASSERT_TRUE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(sub));

    const cy_arrival_t moved = cy_arrival_move(sub);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    cy_message_refcount_dec(moved.message.content);

    TEST_ASSERT_FALSE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(sub));

    cy_subscriber_timeout_set(sub, 10);
    platform.now = 200;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_TRUE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_ERR_LIVENESS, cy_future_error(sub));

    const cy_arrival_t none = cy_arrival_move(sub);
    TEST_ASSERT_NULL(none.message.content);
    TEST_ASSERT_TRUE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_ERR_LIVENESS, cy_future_error(sub));

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_subscriber_borrow_is_nondestructive()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/subscriber/borrow"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/subscriber/borrow"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_best_effort, UINT64_C(0x502), UINT64_C(0xD2), 101, 0xB1U);
    TEST_ASSERT_TRUE(cy_future_done(sub));

    const cy_arrival_t first_borrow = cy_arrival_borrow(sub);
    TEST_ASSERT_NOT_NULL(first_borrow.message.content);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x502), first_borrow.breadcrumb.message_tag);

    const cy_arrival_t second_borrow = cy_arrival_borrow(sub);
    TEST_ASSERT_NOT_NULL(second_borrow.message.content);
    TEST_ASSERT_TRUE(first_borrow.message.content == second_borrow.message.content);
    TEST_ASSERT_TRUE(cy_future_done(sub));

    const cy_arrival_t moved = cy_arrival_move(sub);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    TEST_ASSERT_TRUE(moved.message.content == first_borrow.message.content);
    cy_message_refcount_dec(moved.message.content);

    TEST_ASSERT_FALSE(cy_future_done(sub));

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_subscriber_overwrite_latest_wins_and_count()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/subscriber/overwrite"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/subscriber/overwrite"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_best_effort, UINT64_C(0x601), UINT64_C(0xD3), 110, 0x11U);
    assert_message_counters(0U, 1U);
    dispatch_message(&platform, topic, header_msg_best_effort, UINT64_C(0x602), UINT64_C(0xD3), 111, 0x22U);
    assert_message_counters(1U, 1U); // subscriber_notify() drops the previous retained message.

    TEST_ASSERT_EQUAL_UINT64(UINT64_C(2), cy_arrival_count(sub));
    const cy_arrival_t moved = cy_arrival_move(sub);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x602), moved.breadcrumb.message_tag);

    unsigned char first = 0x00U;
    TEST_ASSERT_EQUAL_size_t(1U, cy_message_read(moved.message.content, 0U, 1U, &first));
    TEST_ASSERT_EQUAL_UINT8(0x22U, first);
    cy_message_refcount_dec(moved.message.content);
    assert_message_counters(2U, 0U);

    TEST_ASSERT_FALSE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    assert_message_counters(2U, 0U);
    platform_deinit(&platform);
}

void test_api_subscriber_arrival_count_excludes_reliable_duplicates()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/subscriber/count"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/subscriber/count"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_reliable, UINT64_C(0x701), UINT64_C(0xD4), 120, 0x31U);
    dispatch_message(&platform, topic, header_msg_reliable, UINT64_C(0x701), UINT64_C(0xD4), 121, 0x32U);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(1), cy_arrival_count(sub));

    const cy_arrival_t first = cy_arrival_move(sub);
    TEST_ASSERT_NOT_NULL(first.message.content);
    unsigned char first_payload = 0x00U;
    TEST_ASSERT_EQUAL_size_t(1U, cy_message_read(first.message.content, 0U, 1U, &first_payload));
    TEST_ASSERT_EQUAL_UINT8(0x31U, first_payload);
    cy_message_refcount_dec(first.message.content);

    dispatch_message(&platform, topic, header_msg_reliable, UINT64_C(0x702), UINT64_C(0xD4), 122, 0x33U);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(2), cy_arrival_count(sub));

    const cy_arrival_t second = cy_arrival_move(sub);
    TEST_ASSERT_NOT_NULL(second.message.content);
    cy_message_refcount_dec(second.message.content);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_subscriber_timeout_set_resets_and_disables_liveness()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    platform.now           = 0;
    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/subscriber/timeout"), 256U);
    TEST_ASSERT_NOT_NULL(sub);

    platform.now = 100;
    TEST_ASSERT_EQUAL_INT64(100, platform.now);
    cy_subscriber_timeout_set(sub, 10);
    TEST_ASSERT_EQUAL_INT(10, cy_subscriber_timeout(sub));

    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_TRUE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_ERR_LIVENESS, cy_future_error(sub));

    cy_subscriber_timeout_set(sub, 1000);
    TEST_ASSERT_EQUAL_INT(1000, cy_subscriber_timeout(sub));
    TEST_ASSERT_FALSE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(sub));

    platform.now = 2000;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_TRUE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_ERR_LIVENESS, cy_future_error(sub));
    TEST_ASSERT_EQUAL_INT64(2000, platform.now);

    cy_subscriber_timeout_set(sub, 0);
    TEST_ASSERT_EQUAL_INT(0, cy_subscriber_timeout(sub));
    TEST_ASSERT_FALSE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(sub));

    platform.now = 5000;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_FALSE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(sub));

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_subscriber_ordered_liveness_can_fire_with_interned_messages()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    platform.now           = 100;
    cy_future_t* const sub = cy_subscribe_ordered(platform.cy, cy_str("rx/subscriber/ordered/liveness"), 256U, 200);
    TEST_ASSERT_NOT_NULL(sub);
    cy_subscriber_timeout_set(sub, 30);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/subscriber/ordered/liveness"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_best_effort, UINT64_C(8), UINT64_C(0xD5), 110, 0x55U);
    TEST_ASSERT_NULL(cy_arrival_borrow(sub).message.content);
    TEST_ASSERT_FALSE(cy_future_done(sub));

    platform.now = 131;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_TRUE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_ERR_LIVENESS, cy_future_error(sub));
    TEST_ASSERT_EQUAL_INT64(131, platform.now);

    cy_subscriber_timeout_set(sub, 0); // clear liveness for deterministic retrieval
    TEST_ASSERT_FALSE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(sub));

    platform.now = 500;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    const cy_arrival_t moved = cy_arrival_move(sub);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(8), moved.breadcrumb.message_tag);
    cy_message_refcount_dec(moved.message.content);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_subscriber_name_and_type_checks()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/subscriber/meta/name"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_TRUE(cy_is_subscriber(sub));
    TEST_ASSERT_FALSE(cy_is_subscriber(nullptr));

    std::array<char, CY_TOPIC_NAME_MAX + 1U> name{};
    std::memset(name.data(), 0xA5, name.size());
    cy_subscriber_name(sub, name.data());
    TEST_ASSERT_EQUAL_STRING("rx/subscriber/meta/name", name.data());

    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("rx/subscriber/meta/name"));
    TEST_ASSERT_NOT_NULL(pub);
    const std::array<unsigned char, 1> payload = { 0x42U };
    const cy_bytes_t                   msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    cy_future_t* const                 fut     = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    TEST_ASSERT_NOT_NULL(fut);
    TEST_ASSERT_FALSE(cy_is_subscriber(fut));

    std::memset(name.data(), 0xA5, name.size());
    cy_subscriber_name(fut, name.data());
    TEST_ASSERT_EQUAL_STRING("", name.data());
    std::memset(name.data(), 0xA5, name.size());
    cy_subscriber_name(nullptr, name.data());
    TEST_ASSERT_EQUAL_STRING("", name.data());
    cy_subscriber_name(sub, nullptr); // NULL-safe

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_subscriber_wrappers_reject_wrong_future_and_null()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    TEST_ASSERT_NULL(cy_subscribe(nullptr, cy_str("rx/subscriber/null"), 64U));
    TEST_ASSERT_NULL(cy_subscribe_ordered(nullptr, cy_str("rx/subscriber/null/ordered"), 64U, 1));
    TEST_ASSERT_NULL(cy_subscribe_ordered(platform.cy, cy_str("rx/subscriber/ordered/invalid"), 64U, -1));

    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("rx/subscriber/wrong/type"));
    TEST_ASSERT_NOT_NULL(pub);
    const std::array<unsigned char, 1> payload = { 0xAAU };
    const cy_bytes_t                   msg     = { .size = payload.size(), .data = payload.data(), .next = nullptr };
    cy_future_t* const                 fut     = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    TEST_ASSERT_NOT_NULL(fut);
    TEST_ASSERT_FALSE(cy_is_subscriber(fut));

    const cy_arrival_t borrow_null  = cy_arrival_borrow(nullptr);
    const cy_arrival_t borrow_wrong = cy_arrival_borrow(fut);
    TEST_ASSERT_NULL(borrow_null.message.content);
    TEST_ASSERT_NULL(borrow_wrong.message.content);

    const cy_arrival_t move_null  = cy_arrival_move(nullptr);
    const cy_arrival_t move_wrong = cy_arrival_move(fut);
    TEST_ASSERT_NULL(move_null.message.content);
    TEST_ASSERT_NULL(move_wrong.message.content);

    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0), cy_arrival_count(nullptr));
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0), cy_arrival_count(fut));
    TEST_ASSERT_EQUAL_INT64(0, cy_subscriber_timeout(nullptr));
    TEST_ASSERT_EQUAL_INT64(0, cy_subscriber_timeout(fut));

    cy_subscriber_timeout_set(nullptr, 123);
    cy_subscriber_timeout_set(fut, 123);

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_subscriber_substitutions_contract()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    static constexpr const char* match_topic_name = "rx/subst/one/two/three";
    static constexpr const char* other_topic_name = "rx/not_subst/topic";

    const auto derive_topic_hash = [&](const char* const topic_name) -> std::uint64_t {
        cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str(topic_name));
        TEST_ASSERT_NOT_NULL(pub);
        const std::uint64_t out = cy_topic_hash(cy_publisher_topic(pub));
        cy_unadvertise(pub);
        TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
        const cy_topic_t* const retained = cy_topic_find_by_name(platform.cy, cy_str(topic_name));
        TEST_ASSERT_NOT_NULL(retained); // Topic retention is lazy: explicit topics are demoted to implicit first.
        TEST_ASSERT_EQUAL_UINT64(out, cy_topic_hash(retained));
        return out;
    };

    const std::uint64_t match_topic_hash = derive_topic_hash(match_topic_name);
    const std::uint64_t other_topic_hash = derive_topic_hash(other_topic_name);

    cy_future_t* const sub_verbatim      = cy_subscribe(platform.cy, cy_str("rx/subst/verbatim"), 256U);
    cy_future_t* const sub_pattern       = cy_subscribe(platform.cy, cy_str("rx/subst/*/>"), 256U);
    cy_future_t* const sub_pattern_2     = cy_subscribe(platform.cy, cy_str("rx/subst/*/>"), 256U);
    cy_future_t* const sub_pattern_other = cy_subscribe(platform.cy, cy_str("rx/other/*"), 256U);
    TEST_ASSERT_NOT_NULL(sub_verbatim);
    TEST_ASSERT_NOT_NULL(sub_pattern);
    TEST_ASSERT_NOT_NULL(sub_pattern_2);
    TEST_ASSERT_NOT_NULL(sub_pattern_other);

    const auto dispatch_gossip =
      [&](const std::uint64_t hash, const char* const topic_name, const std::uint64_t remote_id) {
          std::array<unsigned char, 256U> wire{};
          const std::size_t size = make_gossip_header(wire.data(), wire.size(), 3U, 0, hash, 0U, cy_str(topic_name));
          TEST_ASSERT_TRUE(size > 0U);
          const cy_lane_t lane = { .id = remote_id, .ctx = { { 0 } }, .prio = cy_prio_nominal };
          dispatch_raw(&platform, wire.data(), size, lane, nullptr, 200);
      };
    dispatch_gossip(match_topic_hash, match_topic_name, UINT64_C(0xE1));
    dispatch_gossip(other_topic_hash, other_topic_name, UINT64_C(0xE2));

    const cy_topic_t* const topic_verbatim = cy_topic_find_by_name(platform.cy, cy_str("rx/subst/verbatim"));
    const cy_topic_t* const topic_match    = cy_topic_find_by_name(platform.cy, cy_str(match_topic_name));
    const cy_topic_t* const topic_other    = cy_topic_find_by_name(platform.cy, cy_str(other_topic_name));
    TEST_ASSERT_NOT_NULL(topic_verbatim);
    TEST_ASSERT_NOT_NULL(topic_match);
    TEST_ASSERT_NOT_NULL(topic_other);

    const cy_substitution_set_t verbatim_set = cy_subscriber_substitutions(sub_verbatim, topic_verbatim);
    TEST_ASSERT_EQUAL_size_t(0U, verbatim_set.count);
    TEST_ASSERT_NOT_NULL(verbatim_set.substitutions);

    const cy_substitution_set_t verbatim_null_topic = cy_subscriber_substitutions(sub_verbatim, nullptr);
    TEST_ASSERT_EQUAL_size_t(0U, verbatim_null_topic.count);
    TEST_ASSERT_NOT_NULL(verbatim_null_topic.substitutions);

    const cy_substitution_set_t invalid_future = cy_subscriber_substitutions(nullptr, topic_match);
    TEST_ASSERT_EQUAL_size_t(0U, invalid_future.count);
    TEST_ASSERT_NULL(invalid_future.substitutions);

    const cy_substitution_set_t pattern_null_topic = cy_subscriber_substitutions(sub_pattern, nullptr);
    TEST_ASSERT_EQUAL_size_t(0U, pattern_null_topic.count);
    TEST_ASSERT_NULL(pattern_null_topic.substitutions);

    const cy_substitution_set_t pattern_match = cy_subscriber_substitutions(sub_pattern, topic_match);
    TEST_ASSERT_EQUAL_size_t(3U, pattern_match.count);
    TEST_ASSERT_NOT_NULL(pattern_match.substitutions);
    TEST_ASSERT_EQUAL_size_t(0U, pattern_match.substitutions[0].ordinal);
    TEST_ASSERT_EQUAL_size_t(1U, pattern_match.substitutions[1].ordinal);
    TEST_ASSERT_EQUAL_size_t(1U, pattern_match.substitutions[2].ordinal);
    TEST_ASSERT_EQUAL_size_t(3U, pattern_match.substitutions[0].str.len);
    TEST_ASSERT_EQUAL_size_t(3U, pattern_match.substitutions[1].str.len);
    TEST_ASSERT_EQUAL_size_t(5U, pattern_match.substitutions[2].str.len);
    TEST_ASSERT_EQUAL_MEMORY("one", pattern_match.substitutions[0].str.str, pattern_match.substitutions[0].str.len);
    TEST_ASSERT_EQUAL_MEMORY("two", pattern_match.substitutions[1].str.str, pattern_match.substitutions[1].str.len);
    TEST_ASSERT_EQUAL_MEMORY("three", pattern_match.substitutions[2].str.str, pattern_match.substitutions[2].str.len);

    // Two subscribers share one pattern root. Request substitutions for the non-head subscriber to force a full scan.
    const cy_substitution_set_t pattern_match_non_head = cy_subscriber_substitutions(sub_pattern, topic_match);
    TEST_ASSERT_EQUAL_size_t(3U, pattern_match_non_head.count);
    TEST_ASSERT_NOT_NULL(pattern_match_non_head.substitutions);

    const cy_substitution_set_t pattern_mismatch = cy_subscriber_substitutions(sub_pattern, topic_other);
    TEST_ASSERT_EQUAL_size_t(0U, pattern_mismatch.count);
    TEST_ASSERT_NULL(pattern_mismatch.substitutions);

    // Topic has couplings but not for this pattern root; scan must exhaust and return empty.
    const cy_substitution_set_t pattern_scan_exhaust = cy_subscriber_substitutions(sub_pattern_other, topic_match);
    TEST_ASSERT_EQUAL_size_t(0U, pattern_scan_exhaust.count);
    TEST_ASSERT_NULL(pattern_scan_exhaust.substitutions);

    cy_future_destroy(sub_verbatim);
    cy_future_destroy(sub_pattern);
    cy_future_destroy(sub_pattern_2);
    cy_future_destroy(sub_pattern_other);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_subscriber_liveness_error_clears_on_arrival()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    platform.now           = 0;
    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("rx/subscriber/liveness/recover"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/subscriber/liveness/recover"));
    TEST_ASSERT_NOT_NULL(topic);

    cy_subscriber_timeout_set(sub, 10);
    platform.now = 20;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_TRUE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_ERR_LIVENESS, cy_future_error(sub));

    dispatch_message(&platform, topic, header_msg_best_effort, UINT64_C(0x991), UINT64_C(0xE1), 21, 0x5AU);
    TEST_ASSERT_TRUE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(sub));

    const cy_arrival_t moved = cy_arrival_move(sub);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    cy_message_refcount_dec(moved.message.content);

    TEST_ASSERT_FALSE(cy_future_done(sub));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(sub));

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_subscriber_callback_set_after_completion_invokes_immediately()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    self_unsub_capture_t capture{};
    cy_future_t* const   sub = cy_subscribe(platform.cy, cy_str("rx/subscriber/callback/after"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/subscriber/callback/after"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, header_msg_best_effort, UINT64_C(0x801), UINT64_C(0xD6), 140, 0x44U);
    TEST_ASSERT_TRUE(cy_future_done(sub));

    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &capture;
    cy_future_context_set(sub, ctx);
    cy_future_callback_set(sub, on_arrival_count_only);
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);
    TEST_ASSERT_FALSE(cy_future_done(sub));

    cy_future_callback_set(sub, on_arrival_count_only); // already set -> no immediate re-invocation
    TEST_ASSERT_EQUAL_size_t(1U, capture.count);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}
} // namespace

extern "C" void setUp()
{
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());
    cy_test_message_reset_counters();
}

extern "C" void tearDown() { TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count()); }

int main()
{
    UNITY_BEGIN();
    RUN_TEST(test_api_malformed_header_drops_message);
    RUN_TEST(test_api_inline_msg_rejects_nonzero_incompatibility);
    RUN_TEST(test_api_inline_msg_rejects_invalid_lage);
    RUN_TEST(test_api_inline_msg_rejects_pinned_evictions_lage_mismatch);
    RUN_TEST(test_api_inline_msg_rejects_multicast_subject_mismatch);
    RUN_TEST(test_api_inline_msg_unicast_skips_subject_consistency_check);
    RUN_TEST(test_api_inline_msg_unknown_topic_collision_path_smoke);
    RUN_TEST(test_api_reliable_duplicate_acked_once_to_application);
    RUN_TEST(test_api_ordered_subscriber_timeout_flush);
    RUN_TEST(test_api_unsubscribe_from_own_callback_is_deferred_and_safe);
    RUN_TEST(test_api_unsubscribe_effect_is_applied_on_spin);
    RUN_TEST(test_api_subscriber_destroy_releases_pending_arrival_without_double_free);
    RUN_TEST(test_api_subscriber_move_demotes_done_unless_liveness);
    RUN_TEST(test_api_subscriber_borrow_is_nondestructive);
    RUN_TEST(test_api_subscriber_overwrite_latest_wins_and_count);
    RUN_TEST(test_api_subscriber_arrival_count_excludes_reliable_duplicates);
    RUN_TEST(test_api_subscriber_timeout_set_resets_and_disables_liveness);
    RUN_TEST(test_api_subscriber_ordered_liveness_can_fire_with_interned_messages);
    RUN_TEST(test_api_subscriber_name_and_type_checks);
    RUN_TEST(test_api_subscriber_wrappers_reject_wrong_future_and_null);
    RUN_TEST(test_api_subscriber_substitutions_contract);
    RUN_TEST(test_api_subscriber_liveness_error_clears_on_arrival);
    RUN_TEST(test_api_subscriber_callback_set_after_completion_invokes_immediately);
    return UNITY_END();
}
