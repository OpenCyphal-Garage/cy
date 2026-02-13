#include <cy_platform.h>
#include <unity.h>
#include "helpers.h"
#include "message.h"
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>

namespace {
constexpr std::uint8_t HeaderMsgBestEffort = 0U;
constexpr std::uint8_t HeaderMsgReliable   = 1U;
constexpr std::uint8_t HeaderMsgAck        = 2U;

struct arrival_capture_t
{
    std::size_t                   count{ 0U };
    std::array<std::uint64_t, 16> tags{};
    std::array<unsigned char, 16> first_payload_byte{};
};

struct test_subject_writer_t
{
    cy_subject_writer_t base{};
};

struct test_subject_reader_t
{
    cy_subject_reader_t base{};
    std::size_t         extent{ 0U };
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

    std::size_t                   p2p_count{ 0U };
    std::array<unsigned char, 16> last_p2p{};
    std::size_t                   p2p_extent{ 0U };
};

test_platform_t* platform_from(cy_platform_t* const platform)
{
    return reinterpret_cast<test_platform_t*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

const test_platform_t* platform_from_const(const cy_platform_t* const platform)
{
    return reinterpret_cast<const test_platform_t*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

extern "C" cy_subject_writer_t* platform_subject_writer_new(cy_platform_t* const platform,
                                                            const std::uint32_t  subject_id)
{
    test_platform_t* const self = platform_from(platform);
    auto* const            writer =
      static_cast<test_subject_writer_t*>(guarded_heap_alloc(&self->core_heap, sizeof(test_subject_writer_t)));
    if (writer != nullptr) {
        writer->base.subject_id = subject_id;
    }
    return (writer != nullptr) ? &writer->base : nullptr;
}

extern "C" void platform_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    test_platform_t* const self = platform_from(platform);
    guarded_heap_free(&self->core_heap, writer);
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
    test_platform_t* const self = platform_from(platform);
    auto* const            reader =
      static_cast<test_subject_reader_t*>(guarded_heap_alloc(&self->core_heap, sizeof(test_subject_reader_t)));
    if (reader != nullptr) {
        reader->base.subject_id = subject_id;
        reader->extent          = extent;
    }
    return (reader != nullptr) ? &reader->base : nullptr;
}

extern "C" void platform_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    test_platform_t* const self = platform_from(platform);
    guarded_heap_free(&self->core_heap, reader);
}

extern "C" cy_err_t platform_p2p_send(cy_platform_t* const          platform,
                                      const cy_p2p_context_t* const p2p_context,
                                      const cy_us_t                 deadline,
                                      const std::uint64_t           remote_id,
                                      const cy_bytes_t              message)
{
    (void)p2p_context;
    (void)deadline;
    (void)remote_id;

    test_platform_t* const self = platform_from(platform);
    self->p2p_count++;
    self->last_p2p.fill(0U);

    std::size_t copied = 0U;
    for (const cy_bytes_t* frag = &message; (frag != nullptr) && (copied < self->last_p2p.size()); frag = frag->next) {
        if ((frag->size == 0U) || (frag->data == nullptr)) {
            continue;
        }
        const std::size_t to_copy =
          ((self->last_p2p.size() - copied) < frag->size) ? (self->last_p2p.size() - copied) : frag->size;
        std::memcpy(self->last_p2p.data() + copied, frag->data, to_copy);
        copied += to_copy;
    }
    return CY_OK;
}

extern "C" void platform_p2p_extent_set(cy_platform_t* const platform, const std::size_t extent)
{
    platform_from(platform)->p2p_extent = extent;
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
    test_platform_t* const self = platform_from(platform);
    return guarded_heap_realloc(&self->core_heap, ptr, size);
}

extern "C" std::uint64_t platform_random(cy_platform_t* const platform)
{
    test_platform_t* const self = platform_from(platform);
    self->random_state          = (self->random_state * 6364136223846793005ULL) + 1ULL;
    return self->random_state;
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

extern "C" void on_arrival_capture(cy_subscriber_t* const sub, const cy_arrival_t arrival)
{
    arrival_capture_t* const cap = static_cast<arrival_capture_t*>(cy_subscriber_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(cap);
    TEST_ASSERT(cap->count < cap->tags.size());
    const std::size_t idx = cap->count++;
    cap->tags.at(idx)     = arrival.breadcrumb.message_tag;

    unsigned char first = 0xFFU;
    if (cy_message_read(arrival.message.content, 0U, 1U, &first) == 0U) {
        first = 0xFFU;
    }
    cap->first_payload_byte.at(idx) = first;
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

    self->vtable.p2p_send       = platform_p2p_send;
    self->vtable.p2p_extent_set = platform_p2p_extent_set;

    self->vtable.spin    = platform_spin;
    self->vtable.now     = platform_now;
    self->vtable.realloc = platform_realloc;
    self->vtable.random  = platform_random;

    self->platform.cy                 = nullptr;
    self->platform.subject_id_modulus = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit);
    self->platform.vtable             = &self->vtable;

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
}

void dispatch_message(test_platform_t* const  self,
                      const cy_topic_t* const topic,
                      const std::uint8_t      type,
                      const std::uint64_t     tag,
                      const std::uint64_t     remote_id,
                      const cy_us_t           timestamp,
                      const unsigned char     payload_byte)
{
    std::array<unsigned char, 17> wire{};
    cy_test_make_message_header(wire.data(), type, tag, cy_topic_hash(topic));
    wire[16]                = payload_byte;
    cy_message_t* const msg = cy_test_message_make(&self->message_heap, wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t message{};
    message.timestamp = timestamp;
    message.content   = msg;

    const cy_p2p_context_t p2p = { { 0 } };
    cy_on_message(&self->platform, p2p, remote_id, nullptr, message);
}

void test_api_malformed_header_drops_message()
{
    test_platform_t platform{};
    platform_init(&platform);

    const std::array<unsigned char, 3> wire = { 0x01U, 0x02U, 0x03U };
    cy_message_t* const                msg  = cy_test_message_make(&platform.message_heap, wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t mts{};
    mts.timestamp              = 10;
    mts.content                = msg;
    const cy_p2p_context_t p2p = { { 0 } };

    cy_on_message(&platform.platform, p2p, 1234U, nullptr, mts);
    TEST_ASSERT_EQUAL_size_t(1, cy_test_message_destroy_count());
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());
    TEST_ASSERT_EQUAL_size_t(0, platform.p2p_count);

    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_reliable_duplicate_acked_once_to_application()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    arrival_capture_t      capture{};
    cy_subscriber_t* const sub = cy_subscribe(platform.cy, cy_str("rx/dup"), 256U);
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_subscriber_context_set(sub, context);
    cy_subscriber_callback_set(sub, on_arrival_capture);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/dup"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, HeaderMsgReliable, 0x1234U, 0xAAU, 100, 0x11U);
    dispatch_message(&platform, topic, HeaderMsgReliable, 0x1234U, 0xAAU, 101, 0x22U);

    TEST_ASSERT_EQUAL_size_t(1, capture.count);
    TEST_ASSERT_EQUAL_UINT64(0x1234U, capture.tags[0]);
    TEST_ASSERT_EQUAL_size_t(2, platform.p2p_count);
    TEST_ASSERT_EQUAL_UINT8(HeaderMsgAck, static_cast<std::uint8_t>(platform.last_p2p[0] & 31U));
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());

    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&platform.message_heap));
}

void test_api_ordered_subscriber_timeout_flush()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    arrival_capture_t      capture{};
    cy_subscriber_t* const sub = cy_subscribe_ordered(platform.cy, cy_str("rx/ord"), 256U, 10);
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_subscriber_context_set(sub, context);
    cy_subscriber_callback_set(sub, on_arrival_capture);

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("rx/ord"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, HeaderMsgBestEffort, 8U, 0xBBU, 100, 0x41U);
    dispatch_message(&platform, topic, HeaderMsgBestEffort, 9U, 0xBBU, 101, 0x42U);
    TEST_ASSERT_EQUAL_size_t(0, capture.count);
    TEST_ASSERT_EQUAL_size_t(0, platform.p2p_count);

    platform.now = 1000;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_EQUAL_size_t(2, capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, capture.tags[0]);
    TEST_ASSERT_EQUAL_UINT64(9U, capture.tags[1]);
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());

    platform_deinit(&platform);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&platform.message_heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&platform.message_heap));
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
    RUN_TEST(test_api_reliable_duplicate_acked_once_to_application);
    RUN_TEST(test_api_ordered_subscriber_timeout_flush);
    return UNITY_END();
}
