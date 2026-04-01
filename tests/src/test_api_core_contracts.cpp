#include <cy_platform.h>
#include <rapidhash.h>
#include <unity.h>
#include "api_mock_platform_utils.hpp"
#include "helpers.h"
#include "message.h"
#include <array>
#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

namespace {

constexpr std::uint8_t header_msg_best_effort = 0U;
constexpr std::size_t  header_bytes           = 24U;

struct callback_capture_t
{
    std::size_t calls{ 0U };
    bool        last_done{ false };
    cy_err_t    last_error{ CY_OK };
};

enum class local_op_t
{
    subscribe,
    advertise,
};

struct local_pin_case_t
{
    const char*   canonical_name{ nullptr };
    const char*   first_name{ nullptr };
    local_op_t    first_op{ local_op_t::subscribe };
    const char*   second_name{ nullptr };
    local_op_t    second_op{ local_op_t::subscribe };
    std::uint16_t expected_pin{ 0U };
};

struct test_platform_t final : api_test::test_platform_base_t
{
    cy_err_t    spin_result{ CY_OK };
    std::size_t spin_call_count{ 0U };
    cy_us_t     spin_last_deadline{ 0 };
    cy_us_t     spin_step_limit{ 0 };

    std::size_t multicast_send_count{ 0U };
    std::size_t unicast_send_count{ 0U };
    std::size_t unicast_extent{ 0U };

    std::size_t fail_alloc_count{ 0U };
    std::size_t fail_alloc_size{ 0U };
    std::size_t fail_after_n_allocs{ SIZE_MAX }; // Succeed for N allocations, then fail all subsequent.
    std::size_t alloc_counter{ 0U };
    bool        fail_subject_writer_new{ false };
    bool        fail_subject_reader_new{ false };
};

test_platform_t* platform_from(cy_platform_t* const platform)
{
    return api_test::platform_from<test_platform_t>(platform);
}

const test_platform_t* platform_from_const(const cy_platform_t* const platform)
{
    return api_test::platform_from_const<test_platform_t>(platform);
}

extern "C" cy_subject_writer_t* platform_subject_writer_new(cy_platform_t* const platform,
                                                            const std::uint32_t  subject_id)
{
    const test_platform_t* const self = platform_from_const(platform);
    if (self->fail_subject_writer_new) {
        return nullptr;
    }
    cy_subject_writer_t* const out = api_test::subject_writer_new<test_platform_t>(platform, subject_id);
    if (out != nullptr) {
        test_platform_t* const self_mut = platform_from(platform);
        TEST_ASSERT_EQUAL_INT(0, self_mut->active_writer_subjects.count(subject_id));
        self_mut->active_writer_subjects.insert(subject_id);
    }
    return out;
}

extern "C" void platform_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    api_test::subject_writer_destroy_tracked<test_platform_t>(platform, writer);
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
    const test_platform_t* const self = platform_from_const(platform);
    if (self->fail_subject_reader_new) {
        return nullptr;
    }
    cy_subject_reader_t* const out = api_test::subject_reader_new<test_platform_t>(platform, subject_id, extent);
    if (out != nullptr) {
        test_platform_t* const self_mut = platform_from(platform);
        TEST_ASSERT_EQUAL_INT(0, self_mut->active_reader_subjects.count(subject_id));
        self_mut->active_reader_subjects.insert(subject_id);
    }
    return out;
}

extern "C" void platform_subject_reader_extent_set(cy_platform_t* const       platform,
                                                   cy_subject_reader_t* const reader,
                                                   const std::size_t          extent)
{
    api_test::subject_reader_extent_set_tracked<test_platform_t>(platform, reader, extent);
}

extern "C" void platform_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    api_test::subject_reader_destroy_tracked<test_platform_t>(platform, reader);
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
    if ((ptr == nullptr) && (size > 0U)) {
        if ((self->fail_alloc_count > 0U) && ((self->fail_alloc_size == 0U) || (self->fail_alloc_size == size))) {
            self->fail_alloc_count--;
            return nullptr;
        }
        if (self->alloc_counter >= self->fail_after_n_allocs) {
            return nullptr;
        }
        self->alloc_counter++;
    }
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
    *self     = test_platform_t{};
    self->now = 1000;

    guarded_heap_init(&self->core_heap, UINT64_C(0xFACEB00C12345678));
    guarded_heap_init(&self->message_heap, UINT64_C(0xDEC0DE1234567890));

    self->vtable.subject_writer_new     = platform_subject_writer_new;
    self->vtable.subject_writer_destroy = platform_subject_writer_destroy;
    self->vtable.subject_writer_send    = platform_subject_writer_send;

    self->vtable.subject_reader_new        = platform_subject_reader_new;
    self->vtable.subject_reader_extent_set = platform_subject_reader_extent_set;
    self->vtable.subject_reader_destroy    = platform_subject_reader_destroy;

    self->vtable.unicast            = platform_unicast_send;
    self->vtable.unicast_extent_set = platform_unicast_extent_set;

    self->vtable.spin    = platform_spin;
    self->vtable.now     = platform_now;
    self->vtable.realloc = platform_realloc;
    self->vtable.random  = platform_random;

    api_test::init_platform_base(self->platform, self->vtable);
}

void platform_init(test_platform_t* const self)
{
    platform_prepare(self);
    self->cy = cy_new(&self->platform, cy_str("test"), cy_str_t{ 0, nullptr });
    TEST_ASSERT_NOT_NULL(self->cy);
}

void platform_deinit(test_platform_t* const self) { api_test::standard_deinit(*self); }

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

void dispatch_gossip_unicast(test_platform_t* const self,
                             const std::uint64_t    topic_hash,
                             const std::uint32_t    topic_evictions,
                             const std::int8_t      topic_lage,
                             const cy_str_t         topic_name,
                             const std::uint64_t    remote_id,
                             const cy_us_t          timestamp)
{
    std::array<unsigned char, 256U> wire{};
    const std::size_t               size =
      make_gossip_header(wire.data(), wire.size(), 3U, topic_lage, topic_hash, topic_evictions, topic_name);
    TEST_ASSERT_TRUE(size > 0U);
    cy_message_t* const msg = cy_test_message_make(&self->message_heap, wire.data(), size);
    TEST_ASSERT_NOT_NULL(msg);
    const cy_lane_t lane = { .id = remote_id, .ctx = { { 0 } }, .prio = cy_prio_nominal };
    cy_message_ts_t mts{};
    mts.timestamp = timestamp;
    mts.content   = msg;
    cy_on_message(&self->platform, lane, nullptr, mts);
}

std::uint32_t only_new_subject_id(const std::set<std::uint32_t>& before, const std::set<std::uint32_t>& after)
{
    std::uint32_t out   = 0U;
    std::size_t   count = 0U;
    for (const std::uint32_t subject_id : after) {
        if (!before.contains(subject_id)) {
            out = subject_id;
            count++;
        }
    }
    TEST_ASSERT_EQUAL_size_t(1U, count);
    return out;
}

std::uint32_t probe_topic_subject_id(const test_platform_t& platform,
                                     const char* const      canonical_name,
                                     cy_publisher_t*&       probe)
{
    const std::set<std::uint32_t> before = platform.active_writer_subjects;
    probe                                = cy_advertise(platform.cy, cy_str(canonical_name));
    TEST_ASSERT_NOT_NULL(probe);
    TEST_ASSERT_NOT_NULL(cy_publisher_topic(probe));

    const cy_bytes_t empty = { .size = 0U, .data = nullptr, .next = nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(probe, platform.now + 1000, empty));
    return only_new_subject_id(before, platform.active_writer_subjects);
}

void run_local_pin_case(const local_pin_case_t& tc)
{
    test_platform_t platform{};
    platform_init(&platform);

    std::array<cy_future_t*, 2U>    subs{};
    std::array<cy_publisher_t*, 3U> pubs{};

    const auto perform = [&](const local_op_t op, const char* const name, const std::size_t slot) -> const cy_topic_t* {
        if (op == local_op_t::subscribe) {
            subs.at(slot) = cy_subscribe(platform.cy, cy_str(name), 128U);
            TEST_ASSERT_NOT_NULL(subs.at(slot));
            const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str(tc.canonical_name));
            TEST_ASSERT_NOT_NULL(topic);
            return topic;
        }
        pubs.at(slot) = cy_advertise(platform.cy, cy_str(name));
        TEST_ASSERT_NOT_NULL(pubs.at(slot));
        const cy_topic_t* const topic = cy_publisher_topic(pubs.at(slot));
        TEST_ASSERT_NOT_NULL(topic);
        return topic;
    };

    const cy_topic_t* const topic = perform(tc.first_op, tc.first_name, 0U);
    TEST_ASSERT_TRUE(topic == cy_topic_find_by_name(platform.cy, cy_str(tc.canonical_name)));
    const cy_str_t canonical = cy_topic_name(topic);
    TEST_ASSERT_EQUAL_size_t(std::strlen(tc.canonical_name), canonical.len);
    TEST_ASSERT_EQUAL_MEMORY(tc.canonical_name, canonical.str, canonical.len);

    const cy_topic_t* const same = perform(tc.second_op, tc.second_name, 1U);
    TEST_ASSERT_TRUE(same == topic);
    TEST_ASSERT_TRUE(topic == cy_topic_find_by_name(platform.cy, cy_str(tc.canonical_name)));

    const std::uint32_t subject_id = probe_topic_subject_id(platform, tc.canonical_name, pubs.at(2U));
    TEST_ASSERT_TRUE(cy_publisher_topic(pubs.at(2U)) == topic);
    if (tc.expected_pin == UINT16_MAX) {
        TEST_ASSERT_TRUE(subject_id > CY_SUBJECT_ID_PINNED_MAX);
    } else {
        TEST_ASSERT_EQUAL_UINT32(tc.expected_pin, subject_id);
    }

    for (cy_publisher_t*& pub : pubs) {
        if (pub != nullptr) {
            cy_unadvertise(pub);
            pub = nullptr;
        }
    }
    for (cy_future_t*& sub : subs) {
        if (sub != nullptr) {
            cy_future_destroy(sub);
            sub = nullptr;
        }
    }
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
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
    TEST_ASSERT_EQUAL_INT64(0, platform.spin_last_deadline);

    platform.spin_call_count = 0U;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_until(platform.cy, 1450));
    TEST_ASSERT_EQUAL_size_t(2U, platform.spin_call_count);
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
    // Home and namespace are set at construction time and normalized.
    {
        test_platform_t platform{};
        platform_prepare(&platform);
        platform.cy = cy_new(&platform.platform, cy_str("home//node"), cy_str("ns//a"));
        TEST_ASSERT_NOT_NULL(platform.cy);

        const cy_str_t home = cy_home(platform.cy);
        TEST_ASSERT_EQUAL_size_t(9U, home.len);
        TEST_ASSERT_EQUAL_MEMORY("home/node", home.str, home.len);
        TEST_ASSERT_EQUAL_UINT8('\0', home.str[home.len]);

        const cy_str_t ns = cy_namespace(platform.cy);
        TEST_ASSERT_EQUAL_size_t(4U, ns.len);
        TEST_ASSERT_EQUAL_MEMORY("ns/a", ns.str, ns.len);
        TEST_ASSERT_EQUAL_UINT8('\0', ns.str[ns.len]);

        platform_deinit(&platform);
    }

    // Empty namespace is accepted.
    {
        test_platform_t platform{};
        platform_prepare(&platform);
        platform.cy = cy_new(&platform.platform, cy_str("myhome"), cy_str_t{ 0, nullptr });
        TEST_ASSERT_NOT_NULL(platform.cy);

        const cy_str_t ns = cy_namespace(platform.cy);
        TEST_ASSERT_EQUAL_size_t(0U, ns.len);

        platform_deinit(&platform);
    }

    // NULL cy returns invalid.
    const cy_str_t null_home = cy_home(nullptr);
    const cy_str_t null_ns   = cy_namespace(nullptr);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, null_home.len);
    TEST_ASSERT_EQUAL_size_t(SIZE_MAX, null_ns.len);
    TEST_ASSERT_NULL(null_home.str);
    TEST_ASSERT_NULL(null_ns.str);

    // Empty home is rejected.
    {
        test_platform_t platform{};
        platform_prepare(&platform);
        TEST_ASSERT_NULL(cy_new(&platform.platform, cy_str_t{ 0, nullptr }, cy_str_t{ 0, nullptr }));
        platform_deinit(&platform);
    }

    // Home with invalid characters (space) is rejected.
    {
        test_platform_t platform{};
        platform_prepare(&platform);
        TEST_ASSERT_NULL(cy_new(&platform.platform, cy_str("bad home"), cy_str_t{ 0, nullptr }));
        platform_deinit(&platform);
    }

    // Namespace with invalid characters is rejected.
    {
        test_platform_t platform{};
        platform_prepare(&platform);
        TEST_ASSERT_NULL(cy_new(&platform.platform, cy_str("good"), cy_str("bad ns")));
        platform_deinit(&platform);
    }
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
    for (const void* const ptr : ctx->ptr) {
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
    const cy_str_t h  = cy_str("h");
    const cy_str_t ns = cy_str_t{ 0, nullptr };

    TEST_ASSERT_NULL(cy_new(nullptr, h, ns));

    test_platform_t platform{};
    platform_prepare(&platform);

    platform.platform.vtable = nullptr;
    TEST_ASSERT_NULL(cy_new(&platform.platform, h, ns));
    platform.platform.vtable = &platform.vtable;

    platform.platform.cy = reinterpret_cast<cy_t*>(&platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
    TEST_ASSERT_NULL(cy_new(&platform.platform, h, ns));
    platform.platform.cy = nullptr;

    platform.platform.subject_id_modulus = 8000U; // below minimum
    TEST_ASSERT_NULL(cy_new(&platform.platform, h, ns));
    platform.platform.subject_id_modulus = 8192U; // even
    TEST_ASSERT_NULL(cy_new(&platform.platform, h, ns));
    platform.platform.subject_id_modulus = 24573U; // odd composite
    TEST_ASSERT_NULL(cy_new(&platform.platform, h, ns));
    platform.platform.subject_id_modulus = 65537U; // prime but mod 4 != 3
    TEST_ASSERT_NULL(cy_new(&platform.platform, h, ns));
    platform.platform.subject_id_modulus = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_16bit);

    // Home/namespace argument validation.
    TEST_ASSERT_NULL(cy_new(&platform.platform, cy_str_t{ 0, nullptr }, ns)); // empty home rejected
    TEST_ASSERT_NULL(cy_new(&platform.platform, cy_str("a b"), ns));          // home with space rejected
    TEST_ASSERT_NULL(cy_new(&platform.platform, h, cy_str_t{ 5, nullptr }));  // NULL ns.str with nonzero len rejected

    platform_deinit(&platform);

    test_platform_t fail_alloc{};
    platform_prepare(&fail_alloc);
    fail_alloc.fail_alloc_size  = 0U;
    fail_alloc.fail_alloc_count = 1U;
    TEST_ASSERT_NULL(cy_new(&fail_alloc.platform, h, ns));
    platform_deinit(&fail_alloc);

    test_platform_t fail_reader{};
    platform_prepare(&fail_reader);
    fail_reader.fail_subject_reader_new = true;
    TEST_ASSERT_NULL(cy_new(&fail_reader.platform, h, ns));
    platform_deinit(&fail_reader);

    test_platform_t fail_writer{};
    platform_prepare(&fail_writer);
    fail_writer.fail_subject_writer_new = true;
    TEST_ASSERT_NULL(cy_new(&fail_writer.platform, h, ns));
    platform_deinit(&fail_writer);

    test_platform_t success{};
    platform_prepare(&success);
    success.cy = cy_new(&success.platform, h, ns);
    TEST_ASSERT_NOT_NULL(success.cy);
    platform_deinit(&success);
}

void test_subscriber_name_returns_pin_stripped_name()
{
    test_platform_t platform{};
    platform_init(&platform);

    // Subscribe to a pinned topic. Default namespace is empty, so "foo#123" resolves to "foo" with pin=123.
    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("foo#123"), 256U);
    TEST_ASSERT_NOT_NULL(sub);

    std::array<char, CY_TOPIC_NAME_MAX + 1U> name_buf{};
    cy_subscriber_name(sub, name_buf.data());
    TEST_ASSERT_EQUAL_STRING("foo", name_buf.data());

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_publisher_topic_for_pinned_has_correct_hash()
{
    test_platform_t platform{};
    platform_init(&platform);

    // Advertise on a pinned topic. "bar#100" resolves to name "bar" with pin=100.
    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("bar#100"));
    TEST_ASSERT_NOT_NULL(pub);

    const cy_topic_t* const topic = cy_publisher_topic(pub);
    TEST_ASSERT_NOT_NULL(topic);

    // The topic name must be the resolved name without pin suffix.
    const cy_str_t name = cy_topic_name(topic);
    TEST_ASSERT_EQUAL_size_t(3U, name.len);
    TEST_ASSERT_EQUAL_MEMORY("bar", name.str, name.len);

    // The topic hash must equal rapidhash of the resolved name.
    TEST_ASSERT_EQUAL_UINT64(rapidhash("bar", 3U), cy_topic_hash(topic));

    cy_unadvertise(pub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_topic_find_by_name_uses_resolved_name()
{
    test_platform_t platform{};
    platform_init(&platform);

    // Advertise on a pinned topic. "baz#100" resolves to name "baz" with pin=100.
    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("baz#100"));
    TEST_ASSERT_NOT_NULL(pub);

    // Lookup by the resolved (pin-stripped) name should succeed.
    const cy_topic_t* const found = cy_topic_find_by_name(platform.cy, cy_str("baz"));
    TEST_ASSERT_NOT_NULL(found);

    // Lookup by the original name with pin suffix should fail because the stored name is pin-stripped.
    const cy_topic_t* const not_found = cy_topic_find_by_name(platform.cy, cy_str("baz#100"));
    TEST_ASSERT_NULL(not_found);

    cy_unadvertise(pub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_core_existing_local_topic_keeps_allocation_subscriber_matrix()
{
    static const std::array<local_pin_case_t, 4U> cases = {
        local_pin_case_t{ .canonical_name = "core/pin/sub/existing-nonpinned-then-pinned",
                          .first_name     = "core/pin/sub/existing-nonpinned-then-pinned",
                          .first_op       = local_op_t::subscribe,
                          .second_name    = "core/pin/sub/existing-nonpinned-then-pinned#42",
                          .second_op      = local_op_t::subscribe,
                          .expected_pin   = UINT16_MAX },
        local_pin_case_t{ .canonical_name = "core/pin/sub/existing-higher-then-lower",
                          .first_name     = "core/pin/sub/existing-higher-then-lower#123",
                          .first_op       = local_op_t::subscribe,
                          .second_name    = "core/pin/sub/existing-higher-then-lower#42",
                          .second_op      = local_op_t::subscribe,
                          .expected_pin   = 123U },
        local_pin_case_t{ .canonical_name = "core/pin/sub/existing-pinned-then-nonpinned",
                          .first_name     = "core/pin/sub/existing-pinned-then-nonpinned#42",
                          .first_op       = local_op_t::subscribe,
                          .second_name    = "core/pin/sub/existing-pinned-then-nonpinned",
                          .second_op      = local_op_t::subscribe,
                          .expected_pin   = 42U },
        local_pin_case_t{ .canonical_name = "core/pin/sub/existing-lower-then-higher",
                          .first_name     = "core/pin/sub/existing-lower-then-higher#42",
                          .first_op       = local_op_t::subscribe,
                          .second_name    = "core/pin/sub/existing-lower-then-higher#123",
                          .second_op      = local_op_t::subscribe,
                          .expected_pin   = 42U },
    };

    for (const local_pin_case_t& tc : cases) {
        run_local_pin_case(tc);
    }
}

void test_api_core_existing_local_topic_keeps_allocation_advertiser_matrix()
{
    static const std::array<local_pin_case_t, 4U> cases = {
        local_pin_case_t{ .canonical_name = "core/pin/pub/existing-nonpinned-then-pinned",
                          .first_name     = "core/pin/pub/existing-nonpinned-then-pinned",
                          .first_op       = local_op_t::advertise,
                          .second_name    = "core/pin/pub/existing-nonpinned-then-pinned#42",
                          .second_op      = local_op_t::advertise,
                          .expected_pin   = UINT16_MAX },
        local_pin_case_t{ .canonical_name = "core/pin/pub/existing-higher-then-lower",
                          .first_name     = "core/pin/pub/existing-higher-then-lower#123",
                          .first_op       = local_op_t::advertise,
                          .second_name    = "core/pin/pub/existing-higher-then-lower#42",
                          .second_op      = local_op_t::advertise,
                          .expected_pin   = 123U },
        local_pin_case_t{ .canonical_name = "core/pin/pub/existing-pinned-then-nonpinned",
                          .first_name     = "core/pin/pub/existing-pinned-then-nonpinned#42",
                          .first_op       = local_op_t::advertise,
                          .second_name    = "core/pin/pub/existing-pinned-then-nonpinned",
                          .second_op      = local_op_t::advertise,
                          .expected_pin   = 42U },
        local_pin_case_t{ .canonical_name = "core/pin/pub/existing-lower-then-higher",
                          .first_name     = "core/pin/pub/existing-lower-then-higher#42",
                          .first_op       = local_op_t::advertise,
                          .second_name    = "core/pin/pub/existing-lower-then-higher#123",
                          .second_op      = local_op_t::advertise,
                          .expected_pin   = 42U },
    };

    for (const local_pin_case_t& tc : cases) {
        run_local_pin_case(tc);
    }
}

void test_api_core_existing_local_topic_keeps_allocation_mixed_matrix()
{
    static const std::array<local_pin_case_t, 8U> cases = {
        local_pin_case_t{ .canonical_name = "core/pin/mixed/existing-np-to-pin-sub-then-pub",
                          .first_name     = "core/pin/mixed/existing-np-to-pin-sub-then-pub",
                          .first_op       = local_op_t::subscribe,
                          .second_name    = "core/pin/mixed/existing-np-to-pin-sub-then-pub#42",
                          .second_op      = local_op_t::advertise,
                          .expected_pin   = UINT16_MAX },
        local_pin_case_t{ .canonical_name = "core/pin/mixed/existing-np-to-pin-pub-then-sub",
                          .first_name     = "core/pin/mixed/existing-np-to-pin-pub-then-sub",
                          .first_op       = local_op_t::advertise,
                          .second_name    = "core/pin/mixed/existing-np-to-pin-pub-then-sub#42",
                          .second_op      = local_op_t::subscribe,
                          .expected_pin   = UINT16_MAX },
        local_pin_case_t{ .canonical_name = "core/pin/mixed/existing-high-to-low-sub-then-pub",
                          .first_name     = "core/pin/mixed/existing-high-to-low-sub-then-pub#123",
                          .first_op       = local_op_t::subscribe,
                          .second_name    = "core/pin/mixed/existing-high-to-low-sub-then-pub#42",
                          .second_op      = local_op_t::advertise,
                          .expected_pin   = 123U },
        local_pin_case_t{ .canonical_name = "core/pin/mixed/existing-high-to-low-pub-then-sub",
                          .first_name     = "core/pin/mixed/existing-high-to-low-pub-then-sub#123",
                          .first_op       = local_op_t::advertise,
                          .second_name    = "core/pin/mixed/existing-high-to-low-pub-then-sub#42",
                          .second_op      = local_op_t::subscribe,
                          .expected_pin   = 123U },
        local_pin_case_t{ .canonical_name = "core/pin/mixed/existing-pin-to-unpinned-sub-then-pub",
                          .first_name     = "core/pin/mixed/existing-pin-to-unpinned-sub-then-pub#42",
                          .first_op       = local_op_t::subscribe,
                          .second_name    = "core/pin/mixed/existing-pin-to-unpinned-sub-then-pub",
                          .second_op      = local_op_t::advertise,
                          .expected_pin   = 42U },
        local_pin_case_t{ .canonical_name = "core/pin/mixed/existing-pin-to-unpinned-pub-then-sub",
                          .first_name     = "core/pin/mixed/existing-pin-to-unpinned-pub-then-sub#42",
                          .first_op       = local_op_t::advertise,
                          .second_name    = "core/pin/mixed/existing-pin-to-unpinned-pub-then-sub",
                          .second_op      = local_op_t::subscribe,
                          .expected_pin   = 42U },
        local_pin_case_t{ .canonical_name = "core/pin/mixed/existing-low-to-high-sub-then-pub",
                          .first_name     = "core/pin/mixed/existing-low-to-high-sub-then-pub#42",
                          .first_op       = local_op_t::subscribe,
                          .second_name    = "core/pin/mixed/existing-low-to-high-sub-then-pub#123",
                          .second_op      = local_op_t::advertise,
                          .expected_pin   = 42U },
        local_pin_case_t{ .canonical_name = "core/pin/mixed/existing-low-to-high-pub-then-sub",
                          .first_name     = "core/pin/mixed/existing-low-to-high-pub-then-sub#42",
                          .first_op       = local_op_t::advertise,
                          .second_name    = "core/pin/mixed/existing-low-to-high-pub-then-sub#123",
                          .second_op      = local_op_t::subscribe,
                          .expected_pin   = 42U },
    };

    for (const local_pin_case_t& tc : cases) {
        run_local_pin_case(tc);
    }
}

void test_api_core_advertise_client_oom()
{
    // When the allocator fails during cy_advertise_client, the function should return NULL.
    // This covers the topic_ensure OOM path (lines 2114, 2129).
    test_platform_t platform{};
    platform_init(&platform);

    // Let allocations succeed up to and including the publisher struct, then fail all subsequent.
    // cy_advertise_client does: 1) alloc publisher, 2) topic_ensure (many allocs). We want #1 to succeed, #2 to fail.
    platform.alloc_counter          = 0U;
    platform.fail_after_n_allocs    = 1U; // succeed for 1 alloc (publisher), then fail
    const cy_publisher_t* const pub = cy_advertise_client(platform.cy, cy_str("oom/client/topic"), 64U);
    TEST_ASSERT_NULL(pub);
    platform.fail_after_n_allocs = SIZE_MAX; // re-enable

    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_core_do_publish_oom_subject_writer()
{
    // When the subject writer cannot be created lazily during cy_publish, the publish should fail.
    // This covers lines 2169-2170 (topic_sync_subject_writer failure in do_publish_impl).
    test_platform_t platform{};
    platform_init(&platform);

    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("oom/publish/topic"));
    TEST_ASSERT_NOT_NULL(pub);

    // Make the subject writer creation fail. The writer is created lazily on first publish.
    platform.fail_subject_writer_new = true;

    const cy_bytes_t empty = { .size = 0U, .data = nullptr, .next = nullptr };
    const cy_err_t   err   = cy_publish(pub, platform.now + 1000, empty);
    TEST_ASSERT_NOT_EQUAL(CY_OK, err); // Should fail because subject writer creation fails.

    // Re-enable writer creation and verify publish works now.
    platform.fail_subject_writer_new = false;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, platform.now + 1000, empty));

    cy_unadvertise(pub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_api_core_priority_set_out_of_range()
{
    // Verify that cy_priority_set with an out-of-range value is a no-op (covers branch at line 2801).
    test_platform_t platform{};
    platform_init(&platform);

    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("prio/range/topic"));
    TEST_ASSERT_NOT_NULL(pub);

    cy_priority_set(pub, cy_prio_exceptional);
    TEST_ASSERT_EQUAL_UINT8(cy_prio_exceptional, cy_priority(pub));

    // Use a value that equals CY_PRIO_COUNT (should be >= valid range, so it's rejected).
    cy_prio_t          bad_prio{};
    const std::uint8_t raw_prio = 255U;
    std::memcpy(&bad_prio, &raw_prio, sizeof(raw_prio));
    cy_priority_set(pub, bad_prio);
    TEST_ASSERT_EQUAL_UINT8(cy_prio_exceptional, cy_priority(pub)); // unchanged

    // Also test CY_PRIO_COUNT exactly (the boundary value that should be rejected).
    const auto count_prio = static_cast<std::uint8_t>(CY_PRIO_COUNT);
    std::memcpy(&bad_prio, &count_prio, sizeof(count_prio));
    cy_priority_set(pub, bad_prio);
    TEST_ASSERT_EQUAL_UINT8(cy_prio_exceptional, cy_priority(pub)); // still unchanged

    cy_unadvertise(pub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

/// Exhaustive OOM sweep for cy_advertise: try every possible allocation failure point and ensure clean recovery.
/// This covers lines 1604, 1631-1635, 3632-3634, and other OOM error-handling paths inside topic_new()
/// and ensure_subscriber_root().
void test_api_core_advertise_oom_sweep()
{
    for (std::size_t n = 0U; n < 100U; n++) {
        test_platform_t platform{};
        platform_init(&platform);
        cy_async_error_handler_set(platform.cy, platform_on_async_error);

        platform.alloc_counter       = 0U;
        platform.fail_after_n_allocs = n;

        cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("oom/sweep/advertise"));
        if (pub != nullptr) {
            // Success -- we have found the threshold. All allocations succeeded. Clean up and stop.
            cy_unadvertise(pub);
            TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
            platform_deinit(&platform);
            break;
        }
        // Failed at allocation #n. The library must have cleaned up all partially-allocated state.
        platform.fail_after_n_allocs = SIZE_MAX; // Re-enable allocator.
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
        platform_deinit(&platform); // Asserts heaps are clean -- no leaks.
    }
}

/// Exhaustive OOM sweep for cy_subscribe: try every possible allocation failure point and ensure clean recovery.
/// This covers OOM paths in ensure_subscriber_root() lines 3632-3634 and topic_new() lines 1604, 1631-1635.
void test_api_core_subscribe_oom_sweep()
{
    for (std::size_t n = 0U; n < 100U; n++) {
        test_platform_t platform{};
        platform_init(&platform);
        cy_async_error_handler_set(platform.cy, platform_on_async_error);

        platform.alloc_counter       = 0U;
        platform.fail_after_n_allocs = n;

        cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("oom/sweep/subscribe"), 512U);
        if (sub != nullptr) {
            cy_future_destroy(sub);
            TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
            platform_deinit(&platform);
            break;
        }
        platform.fail_after_n_allocs = SIZE_MAX;
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
        platform_deinit(&platform);
    }
}

/// Exhaustive OOM sweep for cy_subscribe with a pattern (non-verbatim name).
/// Patterns exercise the subscriber_by_pattern index path in ensure_subscriber_root() (lines 3631-3634).
void test_api_core_subscribe_pattern_oom_sweep()
{
    for (std::size_t n = 0U; n < 100U; n++) {
        test_platform_t platform{};
        platform_init(&platform);
        cy_async_error_handler_set(platform.cy, platform_on_async_error);

        platform.alloc_counter       = 0U;
        platform.fail_after_n_allocs = n;

        cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("oom/*/pattern"), 512U);
        if (sub != nullptr) {
            cy_future_destroy(sub);
            TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
            platform_deinit(&platform);
            break;
        }
        platform.fail_after_n_allocs = SIZE_MAX;
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
        platform_deinit(&platform);
    }
}

/// When a second subscriber is added to the same topic with a larger extent, the subject reader extent is grown.
/// This covers line 3586 (reader_grow_extent called with larger extent).
void test_api_core_subscribe_larger_extent_grows_reader()
{
    test_platform_t platform{};
    platform_init(&platform);

    // First subscriber with small extent creates the topic and subject reader.
    cy_future_t* const sub1 = cy_subscribe(platform.cy, cy_str("extent/grow/topic"), 64U);
    TEST_ASSERT_NOT_NULL(sub1);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));

    // Second subscriber with larger extent should trigger reader_grow_extent.
    cy_future_t* const sub2 = cy_subscribe(platform.cy, cy_str("extent/grow/topic"), 4096U);
    TEST_ASSERT_NOT_NULL(sub2);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));

    // Third subscriber with even larger extent should trigger growth again.
    cy_future_t* const sub3 = cy_subscribe(platform.cy, cy_str("extent/grow/topic"), 65536U);
    TEST_ASSERT_NOT_NULL(sub3);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));

    // A subscriber with a smaller extent should not trigger growth (the existing extent is sufficient).
    cy_future_t* const sub4 = cy_subscribe(platform.cy, cy_str("extent/grow/topic"), 32U);
    TEST_ASSERT_NOT_NULL(sub4);

    cy_future_destroy(sub1);
    cy_future_destroy(sub2);
    cy_future_destroy(sub3);
    cy_future_destroy(sub4);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

/// Topic creation OOM in wkv_route for coupling new topic to subscribers.
/// This covers lines 1754-1756 (the wkv_route failure path after topic_new succeeds).
void test_api_core_subscribe_then_advertise_oom_sweep()
{
    for (std::size_t n = 0U; n < 100U; n++) {
        test_platform_t platform{};
        platform_init(&platform);
        cy_async_error_handler_set(platform.cy, platform_on_async_error);

        // Create a pattern subscriber first -- this populates subscriber_by_pattern.
        cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("oom/*/coupling"), 128U);
        TEST_ASSERT_NOT_NULL(sub);

        // Now advertise on a topic that matches the pattern. This triggers topic_ensure -> topic_new
        // and the subsequent wkv_route to couple the new topic with existing pattern subscribers.
        platform.alloc_counter       = 0U;
        platform.fail_after_n_allocs = n;

        cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("oom/test/coupling"));
        if (pub != nullptr) {
            cy_unadvertise(pub);
            platform.fail_after_n_allocs = SIZE_MAX;
            cy_future_destroy(sub);
            TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
            platform_deinit(&platform);
            break;
        }
        platform.fail_after_n_allocs = SIZE_MAX;
        cy_future_destroy(sub);
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
        platform_deinit(&platform);
    }
}

/// Test dedup OOM during on_message for reliable messages.
/// Covers line 3458 (dedup_t allocation fails).
void test_api_core_dedup_oom_on_reliable_message()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_async_error_handler_set(platform.cy, platform_on_async_error);

    cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("oom/dedup/topic"), 256U);
    TEST_ASSERT_NOT_NULL(sub);
    const cy_topic_t* const topic = cy_topic_find_by_name(platform.cy, cy_str("oom/dedup/topic"));
    TEST_ASSERT_NOT_NULL(topic);

    // First, deliver a reliable message successfully so the internal state is set up.
    {
        std::vector<unsigned char> wire(header_bytes + 1U, 0U);
        wire[0] = 1U; // header_msg_reliable
        make_message_header(wire.data(), 1U, UINT64_C(0x1000), cy_topic_hash(topic));
        wire[header_bytes] = 0xAAU;

        cy_message_t* const msg = cy_test_message_make(&platform.message_heap, wire.data(), wire.size());
        TEST_ASSERT_NOT_NULL(msg);

        const cy_lane_t lane = { .id = UINT64_C(0xABC), .ctx = { { 0 } }, .prio = cy_prio_nominal };
        cy_message_ts_t mts{};
        mts.timestamp = platform.now;
        mts.content   = msg;
        cy_on_message(&platform.platform, lane, nullptr, mts);
    }
    TEST_ASSERT_TRUE(cy_future_done(sub));
    const cy_arrival_t arr = cy_arrival_move(sub);
    cy_message_refcount_dec(arr.message.content);

    // Now fail the dedup allocation for a new remote so the dedup_t allocation fails.
    platform.alloc_counter       = 0U;
    platform.fail_after_n_allocs = 0U; // Fail immediately.
    {
        std::vector<unsigned char> wire(header_bytes + 1U, 0U);
        make_message_header(wire.data(), 1U, UINT64_C(0x2000), cy_topic_hash(topic));
        wire[header_bytes] = 0xBBU;

        cy_message_t* const msg = cy_test_message_make(&platform.message_heap, wire.data(), wire.size());
        TEST_ASSERT_NOT_NULL(msg);

        // Use a different remote_id to trigger a new dedup entry allocation.
        const cy_lane_t lane = { .id = UINT64_C(0xDEF), .ctx = { { 0 } }, .prio = cy_prio_nominal };
        cy_message_ts_t mts{};
        mts.timestamp = platform.now + 1;
        mts.content   = msg;
        cy_on_message(&platform.platform, lane, nullptr, mts);
    }
    platform.fail_after_n_allocs = SIZE_MAX;

    // The message should have been dropped (dedup OOM), so the subscriber should NOT have a new message.
    TEST_ASSERT_FALSE(cy_future_done(sub));

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

/// Gossip-triggered topic coupling OOM: a pattern subscriber exists, a gossip creates a new implicit topic
/// matching the pattern, but the coupling allocation fails. Covers lines 1754-1756 (topic_subscribe_if_matching).
void test_api_core_gossip_coupling_oom_sweep()
{
    // We use a sweep to find the allocation threshold where topic_new succeeds but topic_couple fails.
    for (std::size_t n = 0U; n < 100U; n++) {
        test_platform_t platform{};
        platform_init(&platform);
        cy_async_error_handler_set(platform.cy, platform_on_async_error);
        cy_test_message_reset_counters();

        // Create a pattern subscriber first.
        cy_future_t* const sub = cy_subscribe(platform.cy, cy_str("gossip/*/coupling"), 128U);
        TEST_ASSERT_NOT_NULL(sub);

        // The gossip needs to advertise a topic name that matches the pattern and whose hash is unknown.
        // The topic "gossip/test/coupling" matches the pattern "gossip/*/coupling".
        const char* const   topic_name = "gossip/test/coupling";
        const std::uint64_t topic_hash = rapidhash(topic_name, std::strlen(topic_name));

        // Enable OOM at allocation #n, then deliver a gossip that triggers topic_subscribe_if_matching.
        platform.alloc_counter       = 0U;
        platform.fail_after_n_allocs = n;

        dispatch_gossip_unicast(&platform, topic_hash, 0U, 0, cy_str(topic_name), UINT64_C(0xF100), platform.now);

        platform.fail_after_n_allocs = SIZE_MAX;

        // Check if the topic was successfully created (meaning all allocations including coupling succeeded).
        const cy_topic_t* const found = cy_topic_find_by_name(platform.cy, cy_str(topic_name));
        if (found != nullptr) {
            // Success -- the topic was created and coupled. Clean up and stop the sweep.
            cy_future_destroy(sub);
            TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
            platform_deinit(&platform);
            break;
        }
        // Failed at allocation #n. The library must have cleaned up partially-allocated state.
        cy_future_destroy(sub);
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
        platform_deinit(&platform);
    }
}

/// When a non-pinned topic that has published (and thus has a lazily-created pub_writer) receives a gossip
/// that pins it, the pub_writer must be released. Covers lines 1444-1446 (topic_allocate pinned path).
void test_api_core_gossip_pins_topic_with_pub_writer()
{
    test_platform_t platform{};
    platform_init(&platform);
    cy_async_error_handler_set(platform.cy, platform_on_async_error);
    cy_test_message_reset_counters();

    // Advertise a non-pinned topic and publish on it to create the pub_writer lazily.
    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("pin/writer/topic"));
    TEST_ASSERT_NOT_NULL(pub);
    const cy_bytes_t empty = { .size = 0U, .data = nullptr, .next = nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, platform.now + 1000, empty));

    // Confirm the topic exists and get its hash.
    const cy_topic_t* const topic = cy_publisher_topic(pub);
    TEST_ASSERT_NOT_NULL(topic);
    const std::uint64_t hash = cy_topic_hash(topic);

    // Construct a gossip with pinned evictions (UINT32_MAX - 5) and an ordinary in-range wire age.
    // Pinnedness is carried by evictions, so the local topic must still lose arbitration and adopt the pin.
    const auto                              pinned_evictions = static_cast<std::uint32_t>(UINT32_MAX - 5U);
    const cy_str_t                          topic_name       = cy_topic_name(topic);
    std::array<char, CY_TOPIC_NAME_MAX + 1> name_copy{};
    std::memcpy(name_copy.data(), topic_name.str, topic_name.len);

    const cy_str_t gossip_name = { .len = topic_name.len, .str = name_copy.data() };
    dispatch_gossip_unicast(&platform, hash, pinned_evictions, 0, gossip_name, UINT64_C(0xF200), platform.now);

    // After the gossip, the topic should have transitioned to pinned evictions.
    // The pub_writer should have been released (lines 1445-1446).
    // Publish again -- this should lazily recreate the writer for the new (pinned) subject-ID.
    TEST_ASSERT_EQUAL_INT(0, platform.active_writer_subjects.count(5U));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, platform.now + 1000, empty));
    TEST_ASSERT_EQUAL_INT(1, platform.active_writer_subjects.count(5U));

    cy_unadvertise(pub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
}

void test_cy_resolve_uses_node_home_and_namespace()
{
    test_platform_t platform{};
    platform_prepare(&platform);
    platform.cy = cy_new(&platform.platform, cy_str("mynode"), cy_str("ns"));
    TEST_ASSERT_NOT_NULL(platform.cy);

    // Homeful name: ~ expands to the home ("mynode"), namespace is not involved.
    {
        std::array<char, 256U> buf{};
        const cy_resolved_t    r = cy_resolve(platform.cy, cy_str("~/topic"), buf.size(), buf.data());
        TEST_ASSERT_NOT_NULL(r.name.str);
        TEST_ASSERT_EQUAL_size_t(12U, r.name.len); // "mynode/topic"
        TEST_ASSERT_EQUAL_MEMORY("mynode/topic", r.name.str, r.name.len);
        TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
        TEST_ASSERT_TRUE(r.verbatim);
    }

    // Relative name: namespace is prepended.
    {
        std::array<char, 256U> buf{};
        const cy_resolved_t    r = cy_resolve(platform.cy, cy_str("relative/path"), buf.size(), buf.data());
        TEST_ASSERT_NOT_NULL(r.name.str);
        TEST_ASSERT_EQUAL_size_t(16U, r.name.len); // "ns/relative/path"
        TEST_ASSERT_EQUAL_MEMORY("ns/relative/path", r.name.str, r.name.len);
        TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
        TEST_ASSERT_TRUE(r.verbatim);
    }

    // Absolute name: bypass namespace and home entirely, leading separator stripped.
    {
        std::array<char, 256U> buf{};
        const cy_resolved_t    r = cy_resolve(platform.cy, cy_str("/absolute"), buf.size(), buf.data());
        TEST_ASSERT_NOT_NULL(r.name.str);
        TEST_ASSERT_EQUAL_size_t(8U, r.name.len); // "absolute"
        TEST_ASSERT_EQUAL_MEMORY("absolute", r.name.str, r.name.len);
        TEST_ASSERT_EQUAL_UINT16(UINT16_MAX, r.pin);
        TEST_ASSERT_TRUE(r.verbatim);
    }

    platform_deinit(&platform);
}

void test_cy_resolve_with_pin()
{
    test_platform_t platform{};
    platform_prepare(&platform);
    platform.cy = cy_new(&platform.platform, cy_str("mynode"), cy_str("ns"));
    TEST_ASSERT_NOT_NULL(platform.cy);

    // Relative name with pin: namespace prepended, pin stripped and returned separately.
    {
        std::array<char, 256U> buf{};
        const cy_resolved_t    r = cy_resolve(platform.cy, cy_str("topic#123"), buf.size(), buf.data());
        TEST_ASSERT_NOT_NULL(r.name.str);
        TEST_ASSERT_EQUAL_size_t(8U, r.name.len); // "ns/topic"
        TEST_ASSERT_EQUAL_MEMORY("ns/topic", r.name.str, r.name.len);
        TEST_ASSERT_EQUAL_UINT16(123U, r.pin);
        TEST_ASSERT_TRUE(r.verbatim);
    }

    // Homeful name with pin: home expanded, pin stripped and returned separately.
    {
        std::array<char, 256U> buf{};
        const cy_resolved_t    r = cy_resolve(platform.cy, cy_str("~/svc#0"), buf.size(), buf.data());
        TEST_ASSERT_NOT_NULL(r.name.str);
        TEST_ASSERT_EQUAL_size_t(10U, r.name.len); // "mynode/svc"
        TEST_ASSERT_EQUAL_MEMORY("mynode/svc", r.name.str, r.name.len);
        TEST_ASSERT_EQUAL_UINT16(0U, r.pin);
        TEST_ASSERT_TRUE(r.verbatim);
    }

    platform_deinit(&platform);
}

void test_topic_iteration_includes_pinned()
{
    test_platform_t platform{};
    platform_init(&platform);

    // Subscribe to "alpha" (unpinned).
    cy_future_t* const sub_alpha = cy_subscribe(platform.cy, cy_str("alpha"), 128U);
    TEST_ASSERT_NOT_NULL(sub_alpha);

    // Subscribe to "beta#42" (pinned).
    cy_future_t* const sub_beta = cy_subscribe(platform.cy, cy_str("beta#42"), 128U);
    TEST_ASSERT_NOT_NULL(sub_beta);

    // Advertise "gamma#100" (pinned).
    cy_publisher_t* const pub_gamma = cy_advertise(platform.cy, cy_str("gamma#100"));
    TEST_ASSERT_NOT_NULL(pub_gamma);

    // Spin once to process allocations.
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));

    // Iterate all topics and collect their names.
    std::vector<std::string> topic_names;
    for (cy_topic_t* topic = cy_topic_iter_first(platform.cy); topic != nullptr; topic = cy_topic_iter_next(topic)) {
        const cy_str_t name = cy_topic_name(topic);
        topic_names.emplace_back(name.str, name.len);
    }

    // Verify all 3 topics appear in the iteration (order is unspecified).
    const auto has_name = [&](const char* const expected) {
        return std::ranges::any_of(topic_names, [expected](const std::string& name) { return name == expected; });
    };
    TEST_ASSERT_TRUE(has_name("alpha"));
    TEST_ASSERT_TRUE(has_name("beta"));
    TEST_ASSERT_TRUE(has_name("gamma"));

    // Verify each can be found via cy_topic_find_by_name using the resolved (pin-stripped) name.
    TEST_ASSERT_NOT_NULL(cy_topic_find_by_name(platform.cy, cy_str("alpha")));
    TEST_ASSERT_NOT_NULL(cy_topic_find_by_name(platform.cy, cy_str("beta")));
    TEST_ASSERT_NOT_NULL(cy_topic_find_by_name(platform.cy, cy_str("gamma")));

    // Clean up.
    cy_future_destroy(sub_alpha);
    cy_future_destroy(sub_beta);
    cy_unadvertise(pub_gamma);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    platform_deinit(&platform);
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
    RUN_TEST(test_subscriber_name_returns_pin_stripped_name);
    RUN_TEST(test_publisher_topic_for_pinned_has_correct_hash);
    RUN_TEST(test_topic_find_by_name_uses_resolved_name);
    RUN_TEST(test_api_core_existing_local_topic_keeps_allocation_subscriber_matrix);
    RUN_TEST(test_api_core_existing_local_topic_keeps_allocation_advertiser_matrix);
    RUN_TEST(test_api_core_existing_local_topic_keeps_allocation_mixed_matrix);
    RUN_TEST(test_api_core_advertise_client_oom);
    RUN_TEST(test_api_core_do_publish_oom_subject_writer);
    RUN_TEST(test_api_core_priority_set_out_of_range);
    RUN_TEST(test_api_core_advertise_oom_sweep);
    RUN_TEST(test_api_core_subscribe_oom_sweep);
    RUN_TEST(test_api_core_subscribe_pattern_oom_sweep);
    RUN_TEST(test_api_core_subscribe_larger_extent_grows_reader);
    RUN_TEST(test_api_core_subscribe_then_advertise_oom_sweep);
    RUN_TEST(test_api_core_dedup_oom_on_reliable_message);
    RUN_TEST(test_api_core_gossip_coupling_oom_sweep);
    RUN_TEST(test_api_core_gossip_pins_topic_with_pub_writer);
    RUN_TEST(test_cy_resolve_uses_node_home_and_namespace);
    RUN_TEST(test_cy_resolve_with_pin);
    RUN_TEST(test_topic_iteration_includes_pinned);
    return UNITY_END();
}
