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
constexpr cy_us_t ACK_TIMEOUT = 100'000;

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
    std::size_t                   reliable_multicast_count{ 0U };
    bool                          fail_next_reliable_multicast{ false };
    std::uint32_t                 last_multicast_subject_id{ 0U };
    std::array<unsigned char, 19> last_multicast{};

    std::size_t                   p2p_count{ 0U };
    std::array<unsigned char, 17> last_p2p{};
    std::size_t                   p2p_extent{ 0U };
    bool                          fail_next_p2p_send{ false };
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
    if ((self->last_multicast[0] & 63U) == 1U) {
        self->reliable_multicast_count++;
        if (self->fail_next_reliable_multicast) {
            self->fail_next_reliable_multicast = false;
            return CY_ERR_MEDIA;
        }
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
    if (self->fail_next_p2p_send) {
        self->fail_next_p2p_send = false;
        return CY_ERR_MEDIA;
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

struct callback_capture_t
{
    bool               called{ false };
    cy_future_status_t status{ cy_future_pending };
};

extern "C" void on_done_capture(cy_future_t* const fut)
{
    const cy_user_context_t ctx = cy_future_context(fut);
    auto* const             cap = static_cast<callback_capture_t*>(ctx.ptr[0]);
    TEST_ASSERT_NOT_NULL(cap);
    cap->called = true;
    cap->status = cy_future_status(fut);
}

void callback_capture_reset(callback_capture_t& capture)
{
    capture.called = false;
    capture.status = cy_future_pending;
}

void callback_capture_bind(cy_future_t* const fut, callback_capture_t& capture)
{
    callback_capture_reset(capture);
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &capture;
    cy_future_context_set(fut, ctx);
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

void spin_to(test_platform_t& p, const cy_us_t new_now)
{
    p.now = new_now;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(p.cy));
}

cy_publisher_t* setup_publisher(const test_platform_t& p, const char* const topic_name)
{
    cy_publisher_t* const pub = cy_advertise(p.cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(pub);
    cy_ack_timeout_set(pub, ACK_TIMEOUT);
    return pub;
}

std::uint64_t topic_hash_for(const test_platform_t& p, const char* const topic_name)
{
    const cy_topic_t* const topic = cy_topic_find_by_name(p.cy, cy_str(topic_name));
    TEST_ASSERT_NOT_NULL(topic);
    return cy_topic_hash(topic);
}

void build_association(test_platform_t&    p,
                       cy_publisher_t*     pub,
                       const char* const   topic_name,
                       const std::uint64_t remote_id)
{
    const std::uint64_t hash = topic_hash_for(p, topic_name);
    const cy_bytes_t    msg  = { .size = 1U, .data = "\xBB", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, p.now + 5'000'000LL, msg);
    TEST_ASSERT_NOT_NULL(fut);
    const std::uint64_t tag = captured_tag(p);
    dispatch_ack(&p, tag, hash, remote_id, p.now);
    cy_future_destroy(fut);
}

void platform_init(test_platform_t* self);
void platform_deinit(test_platform_t* self);

void test_begin(test_platform_t& p)
{
    platform_init(&p);
    cy_test_message_reset_counters();
}

void test_end(test_platform_t& p)
{
    platform_deinit(&p);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&p.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&p.message_heap));
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

void test_null_publisher()
{
    test_platform_t platform{};
    test_begin(platform);

    const cy_bytes_t empty_message = { .size = 0U, .data = nullptr, .next = nullptr };
    TEST_ASSERT_NULL(cy_publish_reliable(nullptr, 1'000'000, empty_message));

    test_end(platform);
}

void test_negative_deadline()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/negative_deadline");

    const cy_bytes_t empty_message = { .size = 0U, .data = nullptr, .next = nullptr };
    TEST_ASSERT_NULL(cy_publish_reliable(pub, -1, empty_message));

    cy_unadvertise(pub);
    test_end(platform);
}

void test_null_data_nonzero_size()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/null_data_nonzero");

    const cy_bytes_t bad_message = { .size = 1U, .data = nullptr, .next = nullptr };
    TEST_ASSERT_NULL(cy_publish_reliable(pub, 1'000'000, bad_message));

    cy_unadvertise(pub);
    test_end(platform);
}

void test_no_subscribers_single_ack_succeeds()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/no_subscribers_single_ack";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xA1", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0xABCDEF01), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_no_subscribers_timeout_fails()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/no_subscribers_timeout");

    const cy_bytes_t   msg      = { .size = 1U, .data = "\xA2", .next = nullptr };
    const cy_us_t      deadline = platform.now + ACK_TIMEOUT;
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    spin_to(platform, deadline + 1);
    TEST_ASSERT_EQUAL_INT(cy_future_failure, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_no_subscribers_timeout_with_prior_ack_succeeds()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/no_subscribers_timeout_ack";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xA3", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x01020304), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_one_subscriber_acked()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/one_subscriber_acked";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0x1111));

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xA4", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x1111), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_two_subscribers_both_acked()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/two_subscribers_both_acked";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0x2222));
    build_association(platform, pub, TopicName, UINT64_C(0x3333));

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xA5", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x2222), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut));
    dispatch_ack(&platform, tag, hash, UINT64_C(0x3333), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_two_subscribers_one_acks()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/two_subscribers_one_acks";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0x4444));
    build_association(platform, pub, TopicName, UINT64_C(0x5555));

    const cy_bytes_t    msg      = { .size = 1U, .data = "\xA6", .next = nullptr };
    const cy_us_t       deadline = platform.now + ACK_TIMEOUT;
    cy_future_t* const  fut      = cy_publish_reliable(pub, deadline, msg);
    const std::uint64_t tag      = captured_tag(platform);
    const std::uint64_t hash     = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x4444), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut));

    spin_to(platform, deadline + 1);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_two_subscribers_none_ack_timeout()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/two_subscribers_none_ack_timeout";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0x6666));
    build_association(platform, pub, TopicName, UINT64_C(0x7777));

    const cy_bytes_t   msg      = { .size = 1U, .data = "\xA7", .next = nullptr };
    const cy_us_t      deadline = platform.now + ACK_TIMEOUT;
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    spin_to(platform, deadline + 1);
    TEST_ASSERT_EQUAL_INT(cy_future_failure, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_retransmission_on_timeout()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/retransmission_on_timeout";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg      = { .size = 1U, .data = "\xA8", .next = nullptr };
    const cy_us_t       deadline = platform.now + (5 * ACK_TIMEOUT);
    cy_future_t* const  fut      = cy_publish_reliable(pub, deadline, msg);
    const std::uint64_t tag      = captured_tag(platform);
    const std::uint64_t hash     = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    const std::size_t initial_rel_multicast_count = platform.reliable_multicast_count;
    const cy_us_t     t0                          = platform.now;
    spin_to(platform, t0 + ACK_TIMEOUT + 1);
    TEST_ASSERT_TRUE(platform.reliable_multicast_count > initial_rel_multicast_count);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x8888), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_initial_send_failure_returns_null()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/initial_send_failure_returns_null");

    const cy_bytes_t msg                  = { .size = 1U, .data = "\xC0", .next = nullptr };
    platform.fail_next_reliable_multicast = true;
    TEST_ASSERT_NULL(cy_publish_reliable(pub, platform.now + (5 * ACK_TIMEOUT), msg));
    TEST_ASSERT_FALSE(platform.fail_next_reliable_multicast);

    cy_unadvertise(pub);
    test_end(platform);
}

void test_single_remaining_not_last_attempt_stays_multicast()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/single_remaining_not_last_attempt_stays_multicast";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0xA123));

    const cy_bytes_t    msg      = { .size = 1U, .data = "\xC1", .next = nullptr };
    const cy_us_t       deadline = platform.now + (10 * ACK_TIMEOUT);
    cy_future_t* const  fut      = cy_publish_reliable(pub, deadline, msg);
    const std::uint64_t tag      = captured_tag(platform);
    const std::uint64_t hash     = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    const std::size_t p2p_before       = platform.p2p_count;
    const std::size_t multicast_before = platform.reliable_multicast_count;
    const cy_us_t     t0               = platform.now;
    spin_to(platform, t0 + ACK_TIMEOUT + 1);
    TEST_ASSERT_EQUAL_size_t(p2p_before, platform.p2p_count);
    TEST_ASSERT_TRUE(platform.reliable_multicast_count > multicast_before);

    dispatch_ack(&platform, tag, hash, UINT64_C(0xA123), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_retransmission_send_error_does_not_abort_future()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/retransmission_send_error");

    const cy_bytes_t   msg      = { .size = 1U, .data = "\xC2", .next = nullptr };
    const cy_us_t      deadline = platform.now + (5 * ACK_TIMEOUT);
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    cy_async_error_handler_set(platform.cy, nullptr);
    const std::size_t multicast_before    = platform.reliable_multicast_count;
    platform.fail_next_reliable_multicast = true;
    const cy_us_t t0                      = platform.now;
    spin_to(platform, t0 + ACK_TIMEOUT + 1);

    TEST_ASSERT_TRUE(platform.reliable_multicast_count > multicast_before);
    TEST_ASSERT_FALSE(platform.fail_next_reliable_multicast);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut));

    spin_to(platform, deadline + 1);
    TEST_ASSERT_EQUAL_INT(cy_future_failure, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_exponential_backoff_second_timeout()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/exponential_backoff_second_timeout";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg      = { .size = 1U, .data = "\xA9", .next = nullptr };
    const cy_us_t       deadline = platform.now + (100 * ACK_TIMEOUT);
    cy_future_t* const  fut      = cy_publish_reliable(pub, deadline, msg);
    const std::uint64_t tag      = captured_tag(platform);
    const std::uint64_t hash     = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    const cy_us_t t0 = platform.now;
    spin_to(platform, t0 + ACK_TIMEOUT + 1);
    const std::size_t count_1 = platform.reliable_multicast_count;
    spin_to(platform, t0 + ACK_TIMEOUT + 1 + (2 * ACK_TIMEOUT) + 1);
    const std::size_t count_2 = platform.reliable_multicast_count;
    TEST_ASSERT_TRUE(count_2 > count_1);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x9999), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_last_attempt_no_further_retransmission()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/last_attempt_no_further_retransmission";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg      = { .size = 1U, .data = "\xAA", .next = nullptr };
    const cy_us_t       deadline = platform.now + (5 * ACK_TIMEOUT);
    cy_future_t* const  fut      = cy_publish_reliable(pub, deadline, msg);
    const std::uint64_t tag      = captured_tag(platform);
    const std::uint64_t hash     = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    const cy_us_t t0 = platform.now;
    spin_to(platform, t0 + ACK_TIMEOUT + 1);
    const std::size_t count_after_last_attempt = platform.reliable_multicast_count;

    spin_to(platform, t0 + (4 * ACK_TIMEOUT));
    TEST_ASSERT_EQUAL_size_t(count_after_last_attempt, platform.reliable_multicast_count);

    dispatch_ack(&platform, tag, hash, UINT64_C(0xAAAA), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_p2p_retry_single_remaining()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/p2p_retry_single_remaining";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0x1234));
    build_association(platform, pub, TopicName, UINT64_C(0x5678));

    const cy_bytes_t    msg      = { .size = 1U, .data = "\xAB", .next = nullptr };
    const cy_us_t       deadline = platform.now + (5 * ACK_TIMEOUT);
    cy_future_t* const  fut      = cy_publish_reliable(pub, deadline, msg);
    const std::uint64_t tag      = captured_tag(platform);
    const std::uint64_t hash     = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x1234), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut));

    const std::size_t p2p_before = platform.p2p_count;
    const cy_us_t     t0         = platform.now;
    spin_to(platform, t0 + ACK_TIMEOUT + 1);
    TEST_ASSERT_TRUE(platform.p2p_count > p2p_before);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x5678), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_tight_deadline_no_retransmission()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/tight_deadline_no_retransmission");

    const cy_bytes_t   msg      = { .size = 1U, .data = "\xAC", .next = nullptr };
    const cy_us_t      deadline = platform.now + ACK_TIMEOUT;
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);
    TEST_ASSERT_EQUAL_UINT8(1U, static_cast<std::uint8_t>(platform.last_multicast[0] & 63U));

    const std::size_t count_before_spin = platform.reliable_multicast_count;
    spin_to(platform, deadline + 1);
    TEST_ASSERT_EQUAL_INT(cy_future_failure, cy_future_status(fut));
    TEST_ASSERT_EQUAL_size_t(count_before_spin, platform.reliable_multicast_count);

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_tight_deadline_ack_succeeds()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/tight_deadline_ack_succeeds";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg      = { .size = 1U, .data = "\xAD", .next = nullptr };
    const cy_us_t       deadline = platform.now + ACK_TIMEOUT;
    cy_future_t* const  fut      = cy_publish_reliable(pub, deadline, msg);
    const std::uint64_t tag      = captured_tag(platform);
    const std::uint64_t hash     = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0xABCD), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_future_destroy_pending_cancels()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/future_destroy_pending_cancels");

    const cy_bytes_t   msg      = { .size = 1U, .data = "\xAE", .next = nullptr };
    const cy_us_t      deadline = platform.now + (5 * ACK_TIMEOUT);
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    const std::size_t sends_before_destroy = platform.reliable_multicast_count;
    cy_future_destroy(fut);

    spin_to(platform, platform.now + (10 * ACK_TIMEOUT));
    TEST_ASSERT_EQUAL_size_t(sends_before_destroy, platform.reliable_multicast_count);

    cy_unadvertise(pub);
    test_end(platform);
}

void test_future_callback_on_success()
{
    test_platform_t platform{};
    test_begin(platform);
    callback_capture_t capture{};

    static const char* const TopicName = "reliable/future_callback_on_success";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xAF", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    callback_capture_bind(fut, capture);
    cy_future_callback_set(fut, on_done_capture);
    dispatch_ack(&platform, tag, hash, UINT64_C(0x5050), platform.now);

    TEST_ASSERT_TRUE(capture.called);
    TEST_ASSERT_EQUAL_INT(cy_future_success, capture.status);

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_future_callback_on_timeout()
{
    test_platform_t platform{};
    test_begin(platform);
    callback_capture_t capture{};

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/future_callback_on_timeout");

    const cy_bytes_t   msg      = { .size = 1U, .data = "\xB0", .next = nullptr };
    const cy_us_t      deadline = platform.now + ACK_TIMEOUT;
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    callback_capture_bind(fut, capture);
    cy_future_callback_set(fut, on_done_capture);
    spin_to(platform, deadline + 1);

    TEST_ASSERT_TRUE(capture.called);
    TEST_ASSERT_EQUAL_INT(cy_future_failure, capture.status);

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_future_callback_set_after_completion()
{
    test_platform_t platform{};
    test_begin(platform);
    callback_capture_t capture{};

    static const char* const TopicName = "reliable/future_callback_set_after_completion";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xB1", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    callback_capture_bind(fut, capture);
    dispatch_ack(&platform, tag, hash, UINT64_C(0x5151), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    callback_capture_reset(capture);
    cy_future_callback_set(fut, on_done_capture);
    TEST_ASSERT_TRUE(capture.called);
    TEST_ASSERT_EQUAL_INT(cy_future_success, capture.status);

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_future_auto_destroy_callback()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/future_auto_destroy_callback";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xB2", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    cy_future_callback_set(fut, cy_future_destroy);
    dispatch_ack(&platform, tag, hash, UINT64_C(0x5252), platform.now);

    cy_unadvertise(pub);
    test_end(platform);
}

void test_future_context_set_get()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/future_context_set_get");

    const cy_bytes_t   msg = { .size = 1U, .data = "\xB3", .next = nullptr };
    cy_future_t* const fut = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    int               marker = 123;
    cy_user_context_t ctx    = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]               = &marker;
    cy_future_context_set(fut, ctx);
    const cy_user_context_t got = cy_future_context(fut);
    TEST_ASSERT_EQUAL_PTR(&marker, got.ptr[0]);

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_future_result_returns_zero()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/future_result_returns_zero";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xB4", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x5353), platform.now);
    TEST_ASSERT_EQUAL_size_t(0U, cy_future_result(fut, 0U, nullptr));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_unadvertise_cancels_pending_futures()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/unadvertise_cancels_pending_futures");

    const cy_bytes_t   msg      = { .size = 1U, .data = "\xB5", .next = nullptr };
    const cy_us_t      deadline = platform.now + (5 * ACK_TIMEOUT);
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    const std::size_t sends_before_unadvertise = platform.reliable_multicast_count;
    cy_unadvertise(pub);

    spin_to(platform, platform.now + (10 * ACK_TIMEOUT));
    TEST_ASSERT_EQUAL_size_t(sends_before_unadvertise, platform.reliable_multicast_count);

    test_end(platform);
}

void test_multiple_concurrent_futures()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/multiple_concurrent_futures";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t   msg      = { .size = 1U, .data = "\xB6", .next = nullptr };
    const cy_us_t      deadline = platform.now + ACK_TIMEOUT;
    cy_future_t* const fut1     = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut1);
    const std::uint64_t tag1 = captured_tag(platform);

    cy_future_t* const fut2 = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut2);

    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut1));
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut2));

    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    dispatch_ack(&platform, tag1, hash, UINT64_C(0xBEEF), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut1));
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut2));

    spin_to(platform, deadline + 1);
    TEST_ASSERT_EQUAL_INT(cy_future_failure, cy_future_status(fut2));

    cy_future_destroy(fut1);
    cy_future_destroy(fut2);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_ack_builds_association()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/ack_builds_association";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t msg = { .size = 1U, .data = "\xB7", .next = nullptr };

    cy_future_t* const fut1 = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    TEST_ASSERT_NOT_NULL(fut1);
    const std::uint64_t tag1 = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    dispatch_ack(&platform, tag1, hash, UINT64_C(0xAAAA), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut1));
    cy_future_destroy(fut1);

    cy_future_t* const fut2 = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    TEST_ASSERT_NOT_NULL(fut2);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut2));
    const std::uint64_t tag2 = captured_tag(platform);
    dispatch_ack(&platform, tag2, hash, UINT64_C(0xAAAA), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut2));
    cy_future_destroy(fut2);

    cy_unadvertise(pub);
    test_end(platform);
}

void test_ack_from_unknown_remote_still_succeeds()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/ack_from_unknown_remote_still_succeeds";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0xBBBB));

    const cy_bytes_t    msg      = { .size = 1U, .data = "\xB8", .next = nullptr };
    const cy_us_t       deadline = platform.now + ACK_TIMEOUT;
    cy_future_t* const  fut      = cy_publish_reliable(pub, deadline, msg);
    const std::uint64_t tag      = captured_tag(platform);
    const std::uint64_t hash     = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0xCCCC), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut));

    spin_to(platform, deadline + 1);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_duplicate_ack_from_same_remote()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/duplicate_ack_from_same_remote";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0xDDDD));

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xB9", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0xDDDD), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));
    cy_future_destroy(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0xDDDD), platform.now);

    cy_unadvertise(pub);
    test_end(platform);
}

void test_duplicate_ack_while_pending()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/duplicate_ack_while_pending";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0xDA01));
    build_association(platform, pub, TopicName, UINT64_C(0xDA02));

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xC4", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0xDA01), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut));
    dispatch_ack(&platform, tag, hash, UINT64_C(0xDA01), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut));
    dispatch_ack(&platform, tag, hash, UINT64_C(0xDA02), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_ack_future_seqno_ignored()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/ack_future_seqno_ignored";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xBA", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag + 100U, hash, UINT64_C(0xA0A0), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut));

    dispatch_ack(&platform, tag, hash, UINT64_C(0xA0A0), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_ack_invalid_seqno_ignored()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/ack_invalid_seqno_ignored";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg  = { .size = 1U, .data = "\xBB", .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag - 1U, hash, UINT64_C(0xA1A1), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut));

    dispatch_ack(&platform, tag, hash, UINT64_C(0xA1A1), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_send_message_ack_error_path()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/send_message_ack_error_path";
    cy_subscriber_t* const   sub       = cy_subscribe(platform.cy, cy_str(TopicName), 16U);
    TEST_ASSERT_NOT_NULL(sub);

    const std::uint64_t           hash = topic_hash_for(platform, TopicName);
    std::array<unsigned char, 19> wire{};
    wire[0] = 1U;
    wire[1] = 0U;
    for (std::size_t i = 0U; i < 8U; i++) {
        wire.at(2U + i) = static_cast<unsigned char>((UINT64_C(1) >> (i * 8U)) & 0xFFU);
    }
    for (std::size_t i = 0U; i < 8U; i++) {
        wire.at(10U + i) = static_cast<unsigned char>((hash >> (i * 8U)) & 0xFFU);
    }
    wire[18] = 0x5AU;

    cy_message_t* const msg = cy_test_message_make(&platform.message_heap, wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t message{};
    message.timestamp = platform.now;
    message.content   = msg;

    const cy_lane_t lane = { .id = UINT64_C(0xED01), .p2p = { { 0 } }, .prio = cy_prio_nominal };

    const std::size_t p2p_count_before = platform.p2p_count;
    platform.fail_next_p2p_send        = true;
    cy_on_message(&platform.platform, lane, nullptr, message);
    message.timestamp += 1;

    std::array<unsigned char, 19> wire_ok = wire;
    for (std::size_t i = 0U; i < 8U; i++) {
        wire_ok.at(2U + i) = static_cast<unsigned char>((UINT64_C(2) >> (i * 8U)) & 0xFFU);
    }
    wire_ok[18]                = 0x5BU;
    cy_message_t* const msg_ok = cy_test_message_make(&platform.message_heap, wire_ok.data(), wire_ok.size());
    TEST_ASSERT_NOT_NULL(msg_ok);
    message.content = msg_ok;
    cy_on_message(&platform.platform, lane, nullptr, message);

    TEST_ASSERT_EQUAL_size_t(p2p_count_before + 2U, platform.p2p_count);
    TEST_ASSERT_FALSE(platform.fail_next_p2p_send);

    test_end(platform);
}

void test_oom_future_alloc()
{
    test_platform_t platform{};
    test_begin(platform);

    cy_publisher_t* const pub = setup_publisher(platform, "reliable/oom_future_alloc");
    platform_set_fail_after(&platform, 0U);

    const cy_bytes_t msg = { .size = 1U, .data = "\xBC", .next = nullptr };
    TEST_ASSERT_NULL(cy_publish_reliable(pub, platform.now + 1'000'000, msg));

    cy_unadvertise(pub);
    test_end(platform);
}

void test_oom_bitmap_alloc()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/oom_bitmap_alloc";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0xEEEE));
    platform_set_fail_after(&platform, 1U);

    const cy_bytes_t msg = { .size = 1U, .data = "\xBD", .next = nullptr };
    TEST_ASSERT_NULL(cy_publish_reliable(pub, platform.now + 1'000'000, msg));

    cy_unadvertise(pub);
    test_end(platform);
}

void test_oom_bytes_dup()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/oom_bytes_dup";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0xEFEF));
    platform_set_fail_after(&platform, 2U);

    const cy_bytes_t msg = { .size = 1U, .data = "\xBE", .next = nullptr };
    TEST_ASSERT_NULL(cy_publish_reliable(pub, platform.now + (5 * ACK_TIMEOUT), msg));

    cy_unadvertise(pub);
    test_end(platform);
}

void test_empty_message()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/empty_message";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);

    const cy_bytes_t    msg  = { .size = 0U, .data = nullptr, .next = nullptr };
    cy_future_t* const  fut  = cy_publish_reliable(pub, platform.now + 1'000'000, msg);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_ack(&platform, tag, hash, UINT64_C(0xF0F0), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_association_eviction_on_slack()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/association_eviction_on_slack";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0xFFFF));

    const std::size_t assoc_slack_limit = 2U;
    const cy_bytes_t  msg               = { .size = 1U, .data = "\xBF", .next = nullptr };
    for (std::size_t i = 0U; i < assoc_slack_limit; i++) {
        const cy_us_t      deadline = platform.now + ACK_TIMEOUT;
        cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
        TEST_ASSERT_NOT_NULL(fut);

        spin_to(platform, deadline + 1);
        TEST_ASSERT_EQUAL_INT(cy_future_failure, cy_future_status(fut));
        cy_future_destroy(fut);
    }

    const cy_us_t      deadline = platform.now + (5 * ACK_TIMEOUT);
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);
    const std::uint64_t tag  = captured_tag(platform);
    const std::uint64_t hash = topic_hash_for(platform, TopicName);

    dispatch_ack(&platform, tag, hash, UINT64_C(0x9999), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut));

    cy_future_destroy(fut);
    cy_unadvertise(pub);
    test_end(platform);
}

void test_association_at_slack_limit_is_skipped()
{
    test_platform_t platform{};
    test_begin(platform);

    static const char* const TopicName = "reliable/association_at_slack_limit_is_skipped";
    cy_publisher_t* const    pub       = setup_publisher(platform, TopicName);
    build_association(platform, pub, TopicName, UINT64_C(0xCAFE));

    const cy_bytes_t msg = { .size = 1U, .data = "\xC3", .next = nullptr };

    const cy_us_t      deadline_1 = platform.now + ACK_TIMEOUT;
    const cy_us_t      deadline_2 = platform.now + (2 * ACK_TIMEOUT);
    cy_future_t* const fut_1      = cy_publish_reliable(pub, deadline_1, msg);
    cy_future_t* const fut_2      = cy_publish_reliable(pub, deadline_2, msg);
    TEST_ASSERT_NOT_NULL(fut_1);
    TEST_ASSERT_NOT_NULL(fut_2);

    spin_to(platform, deadline_1 + 1);
    TEST_ASSERT_EQUAL_INT(cy_future_failure, cy_future_status(fut_1));
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut_2));

    const cy_us_t      deadline_3 = platform.now + (2 * ACK_TIMEOUT);
    cy_future_t* const fut_3      = cy_publish_reliable(pub, deadline_3, msg);
    TEST_ASSERT_NOT_NULL(fut_3);
    TEST_ASSERT_EQUAL_INT(cy_future_pending, cy_future_status(fut_3));

    spin_to(platform, deadline_2 + 1);
    TEST_ASSERT_EQUAL_INT(cy_future_failure, cy_future_status(fut_2));

    cy_future_t* const  fut_4 = cy_publish_reliable(pub, platform.now + ACK_TIMEOUT, msg);
    const std::uint64_t tag_4 = captured_tag(platform);
    const std::uint64_t hash  = topic_hash_for(platform, TopicName);
    TEST_ASSERT_NOT_NULL(fut_4);

    dispatch_ack(&platform, tag_4, hash, UINT64_C(0xBADA), platform.now);
    TEST_ASSERT_EQUAL_INT(cy_future_success, cy_future_status(fut_4));

    cy_future_destroy(fut_1);
    cy_future_destroy(fut_2);
    cy_future_destroy(fut_3);
    cy_future_destroy(fut_4);
    cy_unadvertise(pub);
    test_end(platform);
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
    RUN_TEST(test_null_publisher);
    RUN_TEST(test_negative_deadline);
    RUN_TEST(test_null_data_nonzero_size);
    RUN_TEST(test_no_subscribers_single_ack_succeeds);
    RUN_TEST(test_no_subscribers_timeout_fails);
    RUN_TEST(test_no_subscribers_timeout_with_prior_ack_succeeds);
    RUN_TEST(test_one_subscriber_acked);
    RUN_TEST(test_two_subscribers_both_acked);
    RUN_TEST(test_two_subscribers_one_acks);
    RUN_TEST(test_two_subscribers_none_ack_timeout);
    RUN_TEST(test_retransmission_on_timeout);
    RUN_TEST(test_initial_send_failure_returns_null);
    RUN_TEST(test_single_remaining_not_last_attempt_stays_multicast);
    RUN_TEST(test_retransmission_send_error_does_not_abort_future);
    RUN_TEST(test_exponential_backoff_second_timeout);
    RUN_TEST(test_last_attempt_no_further_retransmission);
    RUN_TEST(test_p2p_retry_single_remaining);
    RUN_TEST(test_tight_deadline_no_retransmission);
    RUN_TEST(test_tight_deadline_ack_succeeds);
    RUN_TEST(test_future_destroy_pending_cancels);
    RUN_TEST(test_future_callback_on_success);
    RUN_TEST(test_future_callback_on_timeout);
    RUN_TEST(test_future_callback_set_after_completion);
    RUN_TEST(test_future_auto_destroy_callback);
    RUN_TEST(test_future_context_set_get);
    RUN_TEST(test_future_result_returns_zero);
    RUN_TEST(test_unadvertise_cancels_pending_futures);
    RUN_TEST(test_multiple_concurrent_futures);
    RUN_TEST(test_ack_builds_association);
    RUN_TEST(test_ack_from_unknown_remote_still_succeeds);
    RUN_TEST(test_duplicate_ack_from_same_remote);
    RUN_TEST(test_duplicate_ack_while_pending);
    RUN_TEST(test_ack_future_seqno_ignored);
    RUN_TEST(test_ack_invalid_seqno_ignored);
    RUN_TEST(test_send_message_ack_error_path);
    RUN_TEST(test_oom_future_alloc);
    RUN_TEST(test_oom_bitmap_alloc);
    RUN_TEST(test_oom_bytes_dup);
    RUN_TEST(test_empty_message);
    RUN_TEST(test_association_eviction_on_slack);
    RUN_TEST(test_association_at_slack_limit_is_skipped);
    return UNITY_END();
}
