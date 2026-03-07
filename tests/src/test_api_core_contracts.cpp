#include <cy_platform.h>
#include <unity.h>
#include "guarded_heap.h"
#include "helpers.h"
#include "message.h"
#include <array>
#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

namespace {

constexpr std::uint8_t header_msg_best_effort = 0U;
constexpr std::size_t  header_bytes           = 24U;

struct test_subject_writer_t
{
    cy_subject_writer_t base{};
};

struct test_subject_reader_t
{
    cy_subject_reader_t base{};
    std::size_t         extent{ 0U };
};

struct callback_capture_t
{
    std::size_t calls{ 0U };
    bool        last_done{ false };
    cy_err_t    last_error{ CY_OK };
};

struct test_platform_t final
{
    cy_platform_t        platform{};
    cy_platform_vtable_t vtable{};
    guarded_heap_t       core_heap{};
    guarded_heap_t       message_heap{};

    cy_t* cy{ nullptr };

    cy_us_t       now{ 1000 };
    std::uint64_t random_state{ UINT64_C(0x123456789ABCDEF0) };

    cy_err_t    spin_result{ CY_OK };
    std::size_t spin_call_count{ 0U };
    cy_us_t     spin_last_deadline{ 0 };
    cy_us_t     spin_step_limit{ 0 };

    std::size_t multicast_send_count{ 0U };
    std::size_t unicast_send_count{ 0U };
    std::size_t unicast_extent{ 0U };

    std::size_t fail_alloc_count{ 0U };
    std::size_t fail_alloc_size{ 0U };
    bool        fail_subject_writer_new{ false };
    bool        fail_subject_reader_new{ false };
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
    if (self->fail_subject_writer_new) {
        return nullptr;
    }
    auto* const writer =
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
    (void)writer;
    (void)deadline;
    (void)priority;
    (void)message;
    platform_from(platform)->multicast_send_count++;
    return CY_OK;
}

extern "C" cy_subject_reader_t* platform_subject_reader_new(cy_platform_t* const platform,
                                                            const std::uint32_t  subject_id,
                                                            const std::size_t    extent)
{
    test_platform_t* const self = platform_from(platform);
    if (self->fail_subject_reader_new) {
        return nullptr;
    }
    auto* const reader =
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

extern "C" cy_err_t platform_unicast_send(cy_platform_t* const   platform,
                                          const cy_lane_t* const lane,
                                          const cy_us_t          deadline,
                                          const cy_bytes_t       message)
{
    (void)lane;
    (void)deadline;
    (void)message;
    platform_from(platform)->unicast_send_count++;
    return CY_OK;
}

extern "C" void platform_unicast_extent_set(cy_platform_t* const platform, const std::size_t extent)
{
    platform_from(platform)->unicast_extent = extent;
}

extern "C" cy_err_t platform_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    test_platform_t* const self = platform_from(platform);
    self->spin_call_count++;
    self->spin_last_deadline = deadline;
    const cy_us_t step_target =
      (self->spin_step_limit > 0) ? std::min(deadline, self->now + self->spin_step_limit) : deadline;
    self->now = std::max(step_target, self->now);
    return self->spin_result;
}

extern "C" cy_us_t platform_now(cy_platform_t* const platform) { return platform_from_const(platform)->now; }

extern "C" void* platform_realloc(cy_platform_t* const platform, void* const ptr, const std::size_t size)
{
    test_platform_t* const self = platform_from(platform);
    if ((ptr == nullptr) && (size > 0U) && (self->fail_alloc_count > 0U) &&
        ((self->fail_alloc_size == 0U) || (self->fail_alloc_size == size))) {
        self->fail_alloc_count--;
        return nullptr;
    }
    return guarded_heap_realloc(&self->core_heap, ptr, size);
}

extern "C" std::uint64_t platform_random(cy_platform_t* const platform)
{
    test_platform_t* const self = platform_from(platform);
    self->random_state          = (self->random_state * UINT64_C(6364136223846793005)) + UINT64_C(1);
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
}

extern "C" void on_done_capture(cy_future_t* const future)
{
    callback_capture_t* const cap = static_cast<callback_capture_t*>(cy_future_context(future).ptr[0]);
    TEST_ASSERT_NOT_NULL(cap);
    cap->calls++;
    cap->last_done  = cy_future_done(future);
    cap->last_error = cy_future_error(future);
}

void platform_prepare(test_platform_t* const self)
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

    self->platform.cy                 = nullptr;
    self->platform.subject_id_modulus = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit);
    self->platform.vtable             = &self->vtable;
}

void platform_init(test_platform_t* const self)
{
    platform_prepare(self);
    self->cy = cy_new(&self->platform);
    TEST_ASSERT_NOT_NULL(self->cy);
}

void platform_deinit(test_platform_t* const self)
{
    if (self->cy != nullptr) {
        cy_destroy(self->cy);
        self->cy = nullptr;
    }
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self->core_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self->core_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self->message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self->message_heap));
}

void dispatch_best_effort_unicast(test_platform_t* const            self,
                                  const cy_topic_t* const           topic,
                                  const std::uint64_t               tag,
                                  const std::vector<unsigned char>& payload,
                                  const cy_us_t                     timestamp)
{
    TEST_ASSERT_NOT_NULL(topic);
    std::vector<unsigned char> wire(header_bytes + payload.size(), 0U);
    make_message_header(wire.data(), header_msg_best_effort, tag, cy_topic_hash(topic));
    if (!payload.empty()) {
        (void)std::memcpy(wire.data() + header_bytes, payload.data(), payload.size());
    }

    cy_message_t* const msg = cy_test_message_make(&self->message_heap, wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);

    const cy_lane_t lane = { .id = UINT64_C(0xABC), .ctx = { { 0 } }, .prio = cy_prio_nominal };
    cy_message_ts_t mts{};
    mts.timestamp = timestamp;
    mts.content   = msg;
    cy_on_message(&self->platform, lane, nullptr, mts);
}

void test_api_core_time_and_spin_contracts()
{
    test_platform_t platform{};
    platform_init(&platform);

    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_spin_until(nullptr, 0));

    TEST_ASSERT_EQUAL_INT64(1000, cy_now(platform.cy));
    TEST_ASSERT_EQUAL_INT64(0, cy_uptime(platform.cy));

    platform.now = 1250;
    TEST_ASSERT_EQUAL_INT64(1250, cy_now(platform.cy));
    TEST_ASSERT_EQUAL_INT64(250, cy_uptime(platform.cy));

    platform.spin_call_count = 0U;
    platform.spin_result     = CY_OK;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(platform.cy, 900)); // deadline in the past
    TEST_ASSERT_EQUAL_size_t(1U, platform.spin_call_count);
    TEST_ASSERT_EQUAL_INT64(900, platform.spin_last_deadline);

    platform.spin_call_count = 0U;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(platform.cy, 1450));
    TEST_ASSERT_EQUAL_size_t(1U, platform.spin_call_count);
    TEST_ASSERT_EQUAL_INT64(1450, platform.spin_last_deadline);
    TEST_ASSERT_EQUAL_INT64(1450, platform.now);

    platform.spin_call_count = 0U;
    platform.spin_result     = CY_ERR_MEDIA;
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, cy_spin_until(platform.cy, 2000));
    TEST_ASSERT_EQUAL_size_t(1U, platform.spin_call_count);

    platform_deinit(&platform);

    test_platform_t limited_step{};
    platform_init(&limited_step);
    limited_step.spin_step_limit = 100;
    limited_step.now             = 5000;
    limited_step.spin_call_count = 0U;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(limited_step.cy, 5250));
    TEST_ASSERT_EQUAL_size_t(4U, limited_step.spin_call_count);
    platform_deinit(&limited_step);
}

void test_api_core_home_namespace_contracts()
{
    test_platform_t platform{};
    platform_init(&platform);

    cy_str_t home = cy_home(platform.cy);
    cy_str_t ns   = cy_namespace(platform.cy);
    TEST_ASSERT_EQUAL_size_t(0U, home.len);
    TEST_ASSERT_EQUAL_size_t(0U, ns.len);

    const cy_str_t null_home = cy_home(nullptr);
    const cy_str_t null_ns   = cy_namespace(nullptr);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, null_home.len);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, null_ns.len);
    TEST_ASSERT_NULL(null_home.str);
    TEST_ASSERT_NULL(null_ns.str);

    TEST_ASSERT_EQUAL_INT(CY_OK, cy_home_set(platform.cy, cy_str("home//node")));
    home = cy_home(platform.cy);
    TEST_ASSERT_EQUAL_size_t(9U, home.len);
    TEST_ASSERT_EQUAL_MEMORY("home/node", home.str, home.len);

    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_home_set(platform.cy, cy_str("~/bad")));
    home = cy_home(platform.cy);
    TEST_ASSERT_EQUAL_size_t(9U, home.len);
    TEST_ASSERT_EQUAL_MEMORY("home/node", home.str, home.len);

    TEST_ASSERT_EQUAL_INT(CY_OK, cy_namespace_set(platform.cy, cy_str("ns//a")));
    ns = cy_namespace(platform.cy);
    TEST_ASSERT_EQUAL_size_t(4U, ns.len);
    TEST_ASSERT_EQUAL_MEMORY("ns/a", ns.str, ns.len);

    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_namespace_set(platform.cy, cy_str("bad ns")));
    ns = cy_namespace(platform.cy);
    TEST_ASSERT_EQUAL_size_t(4U, ns.len);
    TEST_ASSERT_EQUAL_MEMORY("ns/a", ns.str, ns.len);

    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_home_set(nullptr, cy_str("x")));
    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_namespace_set(nullptr, cy_str("x")));

    platform_deinit(&platform);
}

void test_api_core_priority_ack_and_topic_metadata()
{
    test_platform_t platform{};
    platform_init(&platform);

    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("core/meta/topic"));
    TEST_ASSERT_NOT_NULL(pub);

    cy_topic_t* const topic = cy_publisher_topic(pub);
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_TRUE(cy_topic_owner(topic) == platform.cy);
    TEST_ASSERT_NULL(cy_topic_owner(nullptr));

    cy_user_context_t* const ctx = cy_topic_user_context(topic);
    TEST_ASSERT_NOT_NULL(ctx);
    for (void* const ptr : ctx->ptr) {
        TEST_ASSERT_NULL(ptr);
    }
    int marker  = 0;
    ctx->ptr[0] = &marker;
    TEST_ASSERT_TRUE(cy_topic_user_context(topic)->ptr[0] == &marker);
    TEST_ASSERT_NULL(cy_topic_user_context(nullptr));

    TEST_ASSERT_EQUAL_UINT8(cy_prio_nominal, cy_priority(pub));
    cy_priority_set(pub, cy_prio_exceptional);
    TEST_ASSERT_EQUAL_UINT8(cy_prio_exceptional, cy_priority(pub));

    cy_ack_timeout_set(pub, 12345);
    TEST_ASSERT_EQUAL_INT64(12345, cy_ack_timeout(pub));

    cy_priority_set(pub, cy_prio_high);
    TEST_ASSERT_EQUAL_INT64(12345LL * 8LL, cy_ack_timeout(pub));

    cy_prio_t          invalid_prio{};
    const std::uint8_t bad_prio = 99U;
    std::memcpy(&invalid_prio, &bad_prio, sizeof(bad_prio));
    cy_priority_set(pub, invalid_prio); // invalid no-op
    TEST_ASSERT_EQUAL_UINT8(cy_prio_high, cy_priority(pub));
    const std::int8_t neg_prio = -1;
    std::memcpy(&invalid_prio, &neg_prio, sizeof(neg_prio));
    cy_priority_set(pub, invalid_prio); // invalid no-op
    TEST_ASSERT_EQUAL_UINT8(cy_prio_high, cy_priority(pub));
    const cy_us_t before = cy_ack_timeout(pub);
    cy_ack_timeout_set(pub, 0); // invalid no-op
    TEST_ASSERT_EQUAL_INT64(before, cy_ack_timeout(pub));

    TEST_ASSERT_EQUAL_UINT8(cy_prio_nominal, cy_priority(nullptr));
    cy_priority_set(nullptr, cy_prio_slow);
    TEST_ASSERT_TRUE(cy_ack_timeout(nullptr) < 0);
    cy_ack_timeout_set(nullptr, 12345);
    TEST_ASSERT_NULL(cy_publisher_topic(nullptr));
    cy_unadvertise(nullptr);

    cy_unadvertise(pub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_core_publish_and_request_argument_guards()
{
    test_platform_t platform{};
    platform_init(&platform);

    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("core/guards/topic"));
    TEST_ASSERT_NOT_NULL(pub);

    const cy_bytes_t empty = { .size = 0U, .data = nullptr, .next = nullptr };
    const cy_bytes_t bad   = { .size = 1U, .data = nullptr, .next = nullptr };

    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_publish(nullptr, platform.now, empty));
    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_publish(pub, -1, empty));
    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_publish(pub, platform.now + 1000, bad));

    TEST_ASSERT_NULL(cy_publish_reliable(nullptr, platform.now + 1, empty));
    TEST_ASSERT_NULL(cy_publish_reliable(pub, -1, empty));
    TEST_ASSERT_NULL(cy_publish_reliable(pub, platform.now + 1, bad));

    TEST_ASSERT_NULL(cy_request(nullptr, platform.now + 1, platform.now + 2, empty));
    TEST_ASSERT_NULL(cy_request(pub, -1, platform.now + 2, empty));
    TEST_ASSERT_NULL(cy_request(pub, platform.now + 2, -1, empty));
    TEST_ASSERT_NULL(cy_request(pub, platform.now + 2, platform.now + 3, bad));

    cy_unadvertise(pub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_core_message_contract_and_future_callback_getter()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_test_message_reset_counters();

    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("core/message/topic"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_NULL(cy_future_callback(sub));

    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("core/message/topic"));
    TEST_ASSERT_NOT_NULL(topic);

    const std::vector<unsigned char> payload = { 0xAAU, 0xBBU, 0xCCU };
    dispatch_best_effort_unicast(&platform, topic, UINT64_C(0x102030), payload, 1234);

    TEST_ASSERT_TRUE(cy_future_done(sub));
    const cy_arrival_t borrowed = cy_arrival_borrow(sub);
    TEST_ASSERT_NOT_NULL(borrowed.message.content);
    TEST_ASSERT_EQUAL_size_t(3U, cy_message_size(borrowed.message.content));
    TEST_ASSERT_EQUAL_size_t(0U, cy_message_size(nullptr));

    std::array<unsigned char, 8> out{};
    TEST_ASSERT_EQUAL_size_t(2U, cy_message_read(borrowed.message.content, 1U, out.size(), out.data()));
    TEST_ASSERT_EQUAL_UINT8(0xBBU, out[0]);
    TEST_ASSERT_EQUAL_UINT8(0xCCU, out[1]);
    TEST_ASSERT_EQUAL_size_t(0U, cy_message_read(borrowed.message.content, 0U, 1U, nullptr));
    TEST_ASSERT_EQUAL_size_t(0U, cy_message_read(borrowed.message.content, 100U, 1U, out.data()));
    TEST_ASSERT_EQUAL_size_t(0U, cy_message_read(nullptr, 0U, 1U, out.data()));
    cy_message_t no_vtable{};
    TEST_ASSERT_EQUAL_size_t(0U, cy_message_read(&no_vtable, 0U, 1U, out.data()));
    cy_message_refcount_dec(nullptr);
    cy_message_refcount_dec(&no_vtable);

    callback_capture_t cap{};
    cy_user_context_t  user_ctx = CY_USER_CONTEXT_EMPTY;
    user_ctx.ptr[0]             = &cap;
    cy_future_context_set(sub, user_ctx);
    cy_future_callback_set(sub, on_done_capture); // immediate invocation because already done
    TEST_ASSERT_TRUE(cy_future_callback(sub) == on_done_capture);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.last_done);
    TEST_ASSERT_EQUAL_INT(CY_OK, cap.last_error);

    const cy_arrival_t moved = cy_arrival_move(sub);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    cy_message_refcount_inc(moved.message.content);
    cy_message_refcount_dec(moved.message.content);
    cy_message_refcount_dec(moved.message.content);
    TEST_ASSERT_FALSE(cy_future_done(sub));

    cy_future_callback_set(sub, nullptr);
    TEST_ASSERT_NULL(cy_future_callback(sub));
    cy_future_destroy(nullptr);

    const cy_str_t null_topic_name = cy_topic_name(nullptr);
    TEST_ASSERT_EQUAL_size_t(0U, null_topic_name.len);
    TEST_ASSERT_EQUAL_UINT64(UINT64_MAX, cy_topic_hash(nullptr));
    cy_async_error_handler_set(nullptr, nullptr);

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());

    platform_deinit(&platform);
}

void test_api_core_cy_new_validation_and_failure_paths()
{
    TEST_ASSERT_NULL(cy_new(nullptr));

    test_platform_t platform{};
    platform_prepare(&platform);

    platform.platform.vtable = nullptr;
    TEST_ASSERT_NULL(cy_new(&platform.platform));
    platform.platform.vtable = &platform.vtable;

    platform.platform.cy = reinterpret_cast<cy_t*>(&platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
    TEST_ASSERT_NULL(cy_new(&platform.platform));
    platform.platform.cy = nullptr;

    platform.platform.subject_id_modulus = 8000U; // below minimum
    TEST_ASSERT_NULL(cy_new(&platform.platform));
    platform.platform.subject_id_modulus = 8192U; // even
    TEST_ASSERT_NULL(cy_new(&platform.platform));
    platform.platform.subject_id_modulus = 24573U; // odd composite
    TEST_ASSERT_NULL(cy_new(&platform.platform));
    platform.platform.subject_id_modulus = 65537U; // prime but mod 4 != 3
    TEST_ASSERT_NULL(cy_new(&platform.platform));
    platform.platform.subject_id_modulus = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit);

    platform_deinit(&platform);

    test_platform_t fail_alloc{};
    platform_prepare(&fail_alloc);
    fail_alloc.fail_alloc_size  = 0U;
    fail_alloc.fail_alloc_count = 1U;
    TEST_ASSERT_NULL(cy_new(&fail_alloc.platform));
    platform_deinit(&fail_alloc);

    test_platform_t fail_reader{};
    platform_prepare(&fail_reader);
    fail_reader.fail_subject_reader_new = true;
    TEST_ASSERT_NULL(cy_new(&fail_reader.platform));
    platform_deinit(&fail_reader);

    test_platform_t fail_writer{};
    platform_prepare(&fail_writer);
    fail_writer.fail_subject_writer_new = true;
    TEST_ASSERT_NULL(cy_new(&fail_writer.platform));
    platform_deinit(&fail_writer);

    test_platform_t success{};
    platform_prepare(&success);
    success.cy = cy_new(&success.platform);
    TEST_ASSERT_NOT_NULL(success.cy);
    platform_deinit(&success);
}

} // namespace

extern "C" void setUp()
{
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
    cy_test_message_reset_counters();
}

extern "C" void tearDown() { TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count()); }

int main()
{
    UNITY_BEGIN();
    RUN_TEST(test_api_core_time_and_spin_contracts);
    RUN_TEST(test_api_core_home_namespace_contracts);
    RUN_TEST(test_api_core_priority_ack_and_topic_metadata);
    RUN_TEST(test_api_core_publish_and_request_argument_guards);
    RUN_TEST(test_api_core_message_contract_and_future_callback_getter);
    RUN_TEST(test_api_core_cy_new_validation_and_failure_paths);
    return UNITY_END();
}
