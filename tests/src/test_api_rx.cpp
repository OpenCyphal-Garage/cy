#include <cy_platform.h>
#include <unity.h>
#include "helpers.h"
#include "message.h"
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>

namespace
{
constexpr std::uint8_t HeaderMsgBestEffort = 0U;
constexpr std::uint8_t HeaderMsgReliable   = 1U;
constexpr std::uint8_t HeaderMsgAck        = 2U;

struct arrival_capture_t
{
    std::size_t                         count{0};
    std::array<std::uint64_t, 16>       tags{};
    std::array<unsigned char, 16>       first_payload_byte{};
};

struct test_platform_t
{
    cy_t        cy{};
    cy_vtable_t vtable{};

    cy_us_t now{0};
    std::uint64_t random_state{1U};

    std::size_t p2p_count{0};
    std::array<unsigned char, 16> last_p2p{};
    std::size_t p2p_extent{0};

    std::size_t subscription_error_count{0};
    cy_err_t    last_subscription_error{CY_OK};
};

static test_platform_t* platform_from(cy_t* const cy) { return reinterpret_cast<test_platform_t*>(cy); }

static const test_platform_t* platform_from_const(const cy_t* const cy)
{
    return reinterpret_cast<const test_platform_t*>(cy);
}

extern "C" cy_us_t platform_now(const cy_t* const cy) { return platform_from_const(cy)->now; }

extern "C" void* platform_realloc(cy_t* const cy, void* const ptr, const size_t size)
{
    (void)cy;
    if (size == 0U) {
        std::free(ptr);
        return nullptr;
    }
    return std::realloc(ptr, size);
}

extern "C" std::uint64_t platform_random(cy_t* const cy)
{
    test_platform_t* const self = platform_from(cy);
    self->random_state          = (self->random_state * 6364136223846793005ULL) + 1ULL;
    return self->random_state;
}

extern "C" cy_topic_t* platform_new_topic(cy_t* const cy)
{
    (void)cy;
    return static_cast<cy_topic_t*>(std::calloc(1U, sizeof(cy_topic_t)));
}

extern "C" cy_err_t platform_publish(cy_topic_t* const topic,
                                     const cy_us_t     deadline,
                                     const cy_prio_t   priority,
                                     const cy_bytes_t  message)
{
    (void)topic;
    (void)deadline;
    (void)priority;
    (void)message;
    return CY_OK;
}

extern "C" cy_err_t platform_subscribe(cy_topic_t* const topic, const size_t extent)
{
    (void)topic;
    (void)extent;
    return CY_OK;
}

extern "C" void platform_unsubscribe(cy_topic_t* const topic) { (void)topic; }

extern "C" void platform_topic_destroy(cy_topic_t* const topic) { std::free(topic); }

extern "C" void platform_p2p_extent(cy_t* const cy, const size_t extent) { platform_from(cy)->p2p_extent = extent; }

extern "C" cy_err_t platform_p2p(cy_t* const                  cy,
                                 const cy_p2p_context_t* const p2p_context,
                                 const cy_us_t                 deadline,
                                 const std::uint64_t           remote_id,
                                 const cy_bytes_t              message)
{
    (void)p2p_context;
    (void)deadline;
    (void)remote_id;
    test_platform_t* const self = platform_from(cy);
    self->p2p_count++;
    self->last_p2p.fill(0U);

    std::size_t copied = 0;
    for (const cy_bytes_t* frag = &message; (frag != nullptr) && (copied < self->last_p2p.size()); frag = frag->next) {
        if ((frag->size == 0U) || (frag->data == nullptr)) {
            continue;
        }
        const std::size_t to_copy = (self->last_p2p.size() - copied < frag->size) ? (self->last_p2p.size() - copied)
                                                                                   : frag->size;
        std::memcpy(&self->last_p2p[copied], frag->data, to_copy);
        copied += to_copy;
    }
    return CY_OK;
}

extern "C" void platform_on_subscription_error(cy_t* const cy, cy_topic_t* const topic, const cy_err_t err)
{
    (void)topic;
    test_platform_t* const self = platform_from(cy);
    self->subscription_error_count++;
    self->last_subscription_error = err;
}

extern "C" void on_arrival_capture(cy_subscriber_t* const sub, const cy_arrival_t arrival)
{
    arrival_capture_t* const cap = static_cast<arrival_capture_t*>(cy_subscriber_context(sub).ptr[0]);
    TEST_ASSERT_NOT_NULL(cap);
    TEST_ASSERT(cap->count < cap->tags.size());
    const std::size_t idx = cap->count++;
    cap->tags[idx]        = arrival.breadcrumb.message_tag;

    unsigned char first = 0xFFU;
    if (cy_message_read(arrival.message.content, 0U, 1U, &first) == 0U) {
        first = 0xFFU;
    }
    cap->first_payload_byte[idx] = first;
}

static void platform_init(test_platform_t* const self)
{
    *self = test_platform_t{};
    self->vtable.now                   = platform_now;
    self->vtable.realloc               = platform_realloc;
    self->vtable.random                = platform_random;
    self->vtable.new_topic             = platform_new_topic;
    self->vtable.publish               = platform_publish;
    self->vtable.subscribe             = platform_subscribe;
    self->vtable.unsubscribe           = platform_unsubscribe;
    self->vtable.topic_destroy         = platform_topic_destroy;
    self->vtable.p2p_extent            = platform_p2p_extent;
    self->vtable.p2p                   = platform_p2p;
    self->vtable.on_subscription_error = platform_on_subscription_error;

    const cy_err_t err = cy_new(&self->cy, &self->vtable, wkv_key(""), wkv_key(""), CY_SUBJECT_ID_MODULUS_17bit);
    TEST_ASSERT_EQUAL_UINT8(CY_OK, err);
}

static void dispatch_message(test_platform_t* const self,
                             cy_topic_t* const      topic,
                             const std::uint8_t     type,
                             const std::uint64_t    tag,
                             const std::uint64_t    remote_id,
                             const cy_us_t          timestamp,
                             const unsigned char    payload_byte)
{
    std::array<unsigned char, 17> wire{};
    cy_test_make_message_header(wire.data(), type, tag, cy_topic_hash(topic));
    wire[16] = payload_byte;
    cy_message_t* const msg = cy_test_message_make(wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);

    cy_message_ts_t message;
    message.timestamp = timestamp;
    message.content   = msg;

    const cy_p2p_context_t p2p = { { 0 } };
    cy_on_message(&self->cy, p2p, cy_topic_subject_id(topic), remote_id, message);
}

static void test_api_malformed_header_drops_message(void)
{
    test_platform_t platform;
    platform_init(&platform);

    std::array<unsigned char, 3> wire = { 0x01U, 0x02U, 0x03U };
    cy_message_t* const          msg  = cy_test_message_make(wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);
    cy_message_ts_t       mts;
    mts.timestamp = 10;
    mts.content   = msg;
    const cy_p2p_context_t p2p = { { 0 } };

    cy_on_message(&platform.cy, p2p, 0U, 1234U, mts);
    TEST_ASSERT_EQUAL_size_t(1, cy_test_message_destroy_count());
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());
    TEST_ASSERT_EQUAL_size_t(0, platform.p2p_count);
}

static void test_api_reliable_duplicate_acked_once_to_application(void)
{
    test_platform_t platform;
    platform_init(&platform);
    cy_test_message_reset_counters();

    arrival_capture_t capture{};
    cy_subscriber_t* const sub = cy_subscribe(&platform.cy, wkv_key("rx/dup"), 256U);
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_subscriber_context_set(sub, context);
    cy_subscriber_callback_set(sub, on_arrival_capture);

    cy_topic_t* const topic = cy_topic_find_by_name(&platform.cy, wkv_key("rx/dup"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, HeaderMsgReliable, 0x1234U, 0xAAU, 100, 0x11U);
    dispatch_message(&platform, topic, HeaderMsgReliable, 0x1234U, 0xAAU, 101, 0x22U);

    TEST_ASSERT_EQUAL_size_t(1, capture.count);
    TEST_ASSERT_EQUAL_UINT64(0x1234U, capture.tags[0]);
    TEST_ASSERT_EQUAL_size_t(2, platform.p2p_count);
    TEST_ASSERT_EQUAL_UINT8(HeaderMsgAck, (uint8_t)(platform.last_p2p[0] & 31U));
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());
}

static void test_api_ordered_subscriber_timeout_flush(void)
{
    test_platform_t platform;
    platform_init(&platform);
    cy_test_message_reset_counters();

    arrival_capture_t capture{};
    cy_subscriber_t* const sub = cy_subscribe_ordered(&platform.cy, wkv_key("rx/ord"), 256U, 10);
    TEST_ASSERT_NOT_NULL(sub);

    cy_user_context_t context = CY_USER_CONTEXT_EMPTY;
    context.ptr[0]            = &capture;
    cy_subscriber_context_set(sub, context);
    cy_subscriber_callback_set(sub, on_arrival_capture);

    cy_topic_t* const topic = cy_topic_find_by_name(&platform.cy, wkv_key("rx/ord"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_message(&platform, topic, HeaderMsgBestEffort, 8U, 0xBBU, 100, 0x41U);
    dispatch_message(&platform, topic, HeaderMsgBestEffort, 9U, 0xBBU, 101, 0x42U);
    TEST_ASSERT_EQUAL_size_t(0, capture.count);
    TEST_ASSERT_EQUAL_size_t(0, platform.p2p_count);

    platform.now = 1000;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_update(&platform.cy));
    TEST_ASSERT_EQUAL_size_t(2, capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, capture.tags[0]);
    TEST_ASSERT_EQUAL_UINT64(9U, capture.tags[1]);
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());
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
