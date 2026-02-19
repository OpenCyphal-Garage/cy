#include <cy_platform.h>
#include <unity.h>
#include "guarded_heap.h"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>

namespace {
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

    std::size_t fail_after{ std::numeric_limits<std::size_t>::max() };
    std::size_t new_alloc_count{ 0U };

    std::size_t                   multicast_count{ 0U };
    std::uint32_t                 last_multicast_subject_id{ 0U };
    std::array<unsigned char, 19> last_multicast{};

    std::size_t                   p2p_count{ 0U };
    std::array<unsigned char, 17> last_p2p{};
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
    (void)deadline;
    (void)priority;
    test_platform_t* const self = platform_from(platform);
    self->multicast_count++;
    self->last_multicast_subject_id = (writer != nullptr) ? writer->subject_id : 0U;
    self->last_multicast.fill(0U);

    std::size_t copied = 0U;
    for (const cy_bytes_t* frag = &message; (frag != nullptr) && (copied < self->last_multicast.size());
         frag                   = frag->next) {
        if ((frag->size == 0U) || (frag->data == nullptr)) {
            continue;
        }
        const std::size_t to_copy = std::min(self->last_multicast.size() - copied, frag->size);
        std::memcpy(self->last_multicast.data() + copied, frag->data, to_copy);
        copied += to_copy;
    }
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

extern "C" cy_err_t platform_p2p_send(cy_platform_t* const   platform,
                                      const cy_lane_t* const lane,
                                      const cy_us_t          deadline,
                                      const cy_bytes_t       message)
{
    (void)lane;
    (void)deadline;

    test_platform_t* const self = platform_from(platform);
    self->p2p_count++;
    self->last_p2p.fill(0U);

    std::size_t copied = 0U;
    for (const cy_bytes_t* frag = &message; (frag != nullptr) && (copied < self->last_p2p.size()); frag = frag->next) {
        if ((frag->size == 0U) || (frag->data == nullptr)) {
            continue;
        }
        const std::size_t to_copy = std::min(self->last_p2p.size() - copied, frag->size);
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

extern "C" cy_us_t platform_now(cy_platform_t* const platform) { return platform_from_const(platform)->now; }

extern "C" void* platform_realloc(cy_platform_t* const platform, void* const ptr, const std::size_t size)
{
    test_platform_t* const self = platform_from(platform);
    if ((ptr == nullptr) && (size > 0U)) {
        if (self->new_alloc_count >= self->fail_after) {
            return nullptr;
        }
        self->new_alloc_count++;
    }
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
    (void)error;
    (void)line_number;
    TEST_FAIL_MESSAGE("Unexpected async error callback invocation");
}

cy_message_t* make_ack_message(test_platform_t* const self, const std::uint64_t tag, const std::uint64_t topic_hash)
{
    std::array<unsigned char, 17> wire{};
    wire[0] = 2U;
    for (std::size_t i = 0U; i < 8U; i++) {
        wire.at(1U + i) = static_cast<unsigned char>((tag >> (i * 8U)) & 0xFFU);
    }
    for (std::size_t i = 0U; i < 8U; i++) {
        wire.at(9U + i) = static_cast<unsigned char>((topic_hash >> (i * 8U)) & 0xFFU);
    }
    return cy_test_message_make(&self->message_heap, wire.data(), wire.size());
}

void dispatch_ack(test_platform_t* const self,
                  const std::uint64_t    tag,
                  const std::uint64_t    topic_hash,
                  const std::uint64_t    remote_id,
                  const cy_us_t          timestamp)
{
    cy_message_t* const msg = make_ack_message(self, tag, topic_hash);
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t message{};
    message.timestamp = timestamp;
    message.content   = msg;

    const cy_lane_t lane = { .id = remote_id, .p2p = { { 0 } }, .prio = cy_prio_nominal };
    cy_on_message(&self->platform, lane, nullptr, message);
}

void platform_set_fail_after(test_platform_t* const self, const std::size_t fail_after)
{
    self->fail_after      = fail_after;
    self->new_alloc_count = 0U;
}

std::uint64_t captured_tag(const test_platform_t& self)
{
    std::uint64_t tag = 0U;
    for (std::size_t i = 0U; i < 8U; i++) {
        tag |= static_cast<std::uint64_t>(self.last_multicast.at(2U + i)) << (i * 8U);
    }
    return tag;
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

void test_null_args()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    const cy_bytes_t empty_message = { .size = 0U, .data = nullptr, .next = nullptr };
    TEST_ASSERT_NULL(cy_publish_reliable(nullptr, 1000000, empty_message));

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
    RUN_TEST(test_null_args);
    return UNITY_END();
}
