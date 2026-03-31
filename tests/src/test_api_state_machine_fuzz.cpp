#include <cy_platform.h>
#include <unity.h>
#include "api_mock_platform_utils.hpp"
#include "guarded_heap.h"
#include "message.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <set>
#include <vector>

namespace {

struct test_platform_t final
{
    cy_platform_t        platform{};
    cy_platform_vtable_t vtable{};
    guarded_heap_t       core_heap{};
    guarded_heap_t       message_heap{};
    cy_t*                cy{ nullptr };

    cy_us_t       now{ 0 };
    std::uint64_t random_state{ UINT64_C(0xD1CEB00BCAFEBEEF) };

    std::set<std::uint32_t> active_reader_subjects;
    std::set<std::uint32_t> active_writer_subjects;
};

struct future_entry_t final
{
    cy_future_t* fut{ nullptr };
    std::size_t  pub_slot{ 0U };
};

test_platform_t* platform_from(cy_platform_t* const platform)
{
    return api_test::platform_from<test_platform_t>(platform);
}

extern "C" cy_subject_writer_t* platform_subject_writer_new(cy_platform_t* const platform,
                                                            const std::uint32_t  subject_id)
{
    cy_subject_writer_t* const out = api_test::subject_writer_new<test_platform_t>(platform, subject_id);
    if (out != nullptr) {
        test_platform_t* const self = platform_from(platform);
        TEST_ASSERT_EQUAL_INT(0, self->active_writer_subjects.count(subject_id));
        self->active_writer_subjects.insert(subject_id);
    }
    return out;
}

extern "C" void platform_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    test_platform_t* const self = platform_from(platform);
    TEST_ASSERT_EQUAL_INT(1, self->active_writer_subjects.erase(writer->subject_id));
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
    cy_subject_reader_t* const out = api_test::subject_reader_new<test_platform_t>(platform, subject_id, extent);
    if (out != nullptr) {
        test_platform_t* const self = platform_from(platform);
        TEST_ASSERT_EQUAL_INT(0, self->active_reader_subjects.count(subject_id));
        self->active_reader_subjects.insert(subject_id);
    }
    return out;
}

extern "C" void platform_subject_reader_extent_set(cy_platform_t* const       platform,
                                                   cy_subject_reader_t* const reader,
                                                   const std::size_t          extent)
{
    test_platform_t* const self = platform_from(platform);
    TEST_ASSERT_EQUAL_INT(1, self->active_reader_subjects.count(reader->subject_id));
    api_test::subject_reader_extent_set<test_platform_t>(platform, reader, extent);
}

extern "C" void platform_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    test_platform_t* const self = platform_from(platform);
    TEST_ASSERT_EQUAL_INT(1, self->active_reader_subjects.erase(reader->subject_id));
    api_test::subject_reader_destroy<test_platform_t>(platform, reader);
}

extern "C" cy_err_t platform_unicast_send(cy_platform_t* const   platform,
                                          const cy_lane_t* const lane,
                                          const cy_us_t          deadline,
                                          const cy_bytes_t       message)
{
    (void)platform;
    (void)lane;
    (void)deadline;
    (void)message;
    return CY_OK;
}

extern "C" void platform_unicast_extent_set(cy_platform_t* const platform, const std::size_t extent)
{
    (void)platform;
    (void)extent;
}

extern "C" cy_err_t platform_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    test_platform_t* const self = platform_from(platform);
    self->now                   = std::max(self->now, deadline);
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

void platform_init(test_platform_t* const self)
{
    *self = test_platform_t{};
    guarded_heap_init(&self->core_heap, UINT64_C(0xFACEB00C12345678));
    guarded_heap_init(&self->message_heap, UINT64_C(0xDEC0DE1234567890));

    self->vtable.subject_writer_new        = platform_subject_writer_new;
    self->vtable.subject_writer_destroy    = platform_subject_writer_destroy;
    self->vtable.subject_writer_send       = platform_subject_writer_send;
    self->vtable.subject_reader_new        = platform_subject_reader_new;
    self->vtable.subject_reader_extent_set = platform_subject_reader_extent_set;
    self->vtable.subject_reader_destroy    = platform_subject_reader_destroy;
    self->vtable.unicast                   = platform_unicast_send;
    self->vtable.unicast_extent_set        = platform_unicast_extent_set;
    self->vtable.spin                      = platform_spin;
    self->vtable.now                       = platform_now;
    self->vtable.realloc                   = platform_realloc;
    self->vtable.random                    = platform_random;

    api_test::init_platform_base(self->platform, self->vtable);
    self->cy = cy_new(&self->platform);
    TEST_ASSERT_NOT_NULL(self->cy);
}

void platform_deinit(test_platform_t* const self)
{
    if (self->cy != nullptr) {
        cy_destroy(self->cy);
        self->cy = nullptr;
    }
    api_test::assert_heaps_clean(self->core_heap, self->message_heap);
}

std::uint64_t rng_next(std::uint64_t& state)
{
    state = (state * UINT64_C(2862933555777941757)) + UINT64_C(3037000493);
    return state;
}

std::size_t rng_mod(std::uint64_t& state, const std::size_t modulo)
{
    TEST_ASSERT_TRUE(modulo > 0U);
    return static_cast<std::size_t>(rng_next(state) % modulo);
}

void destroy_future_entry(std::vector<future_entry_t>& futures, const std::size_t index)
{
    TEST_ASSERT_TRUE(index < futures.size());
    if (futures.at(index).fut != nullptr) {
        cy_future_destroy(futures.at(index).fut);
    }
    futures.erase(futures.begin() + static_cast<std::ptrdiff_t>(index));
}

void destroy_futures_for_pub(std::vector<future_entry_t>& futures, const std::size_t pub_slot)
{
    for (std::ptrdiff_t i = static_cast<std::ptrdiff_t>(futures.size()) - 1; i >= 0; i--) {
        if (futures.at(static_cast<std::size_t>(i)).pub_slot == pub_slot) {
            destroy_future_entry(futures, static_cast<std::size_t>(i));
        }
    }
}

void test_api_state_machine_fuzz_lifecycle()
{
    test_platform_t platform{};
    platform_init(&platform);

    static constexpr std::array<const char*, 8> topics = {
        "sm/a", "sm/b", "sm/c", "sm/d", "sm/e", "sm/f", "sm/g", "sm/h",
    };

    std::array<cy_publisher_t*, 4> publishers  = { nullptr, nullptr, nullptr, nullptr };
    std::array<cy_future_t*, 4>    subscribers = { nullptr, nullptr, nullptr, nullptr };
    std::vector<future_entry_t>    futures{};
    futures.reserve(64U);

    std::uint64_t rng = UINT64_C(0x1BADB002FEEDC0DE);
    for (std::size_t step = 0U; step < 600U; step++) {
        const auto        op    = rng_mod(rng, 12U);
        const auto        slot  = rng_mod(rng, publishers.size());
        const char* const topic = topics.at(rng_mod(rng, topics.size()));
        auto* const       pub   = publishers.at(slot);

        switch (op) {
            case 0: { // create publisher
                if (pub == nullptr) {
                    publishers.at(slot) = cy_advertise_client(platform.cy, cy_str(topic), 96U);
                }
                break;
            }
            case 1: { // destroy publisher
                if (pub != nullptr) {
                    destroy_futures_for_pub(futures, slot);
                    cy_unadvertise(pub);
                    publishers.at(slot) = nullptr;
                }
                break;
            }
            case 2: { // create subscriber
                const auto sub_slot = rng_mod(rng, subscribers.size());
                if (subscribers.at(sub_slot) == nullptr) {
                    subscribers.at(sub_slot) = cy_subscribe(platform.cy, cy_str(topic), 128U);
                }
                break;
            }
            case 3: { // destroy subscriber
                const auto sub_slot = rng_mod(rng, subscribers.size());
                if (subscribers.at(sub_slot) != nullptr) {
                    cy_future_destroy(subscribers.at(sub_slot));
                    subscribers.at(sub_slot) = nullptr;
                }
                break;
            }
            case 4: { // publish best-effort
                if (pub != nullptr) {
                    const std::array<unsigned char, 2> payload = {
                        static_cast<unsigned char>(step & 0xFFU),
                        static_cast<unsigned char>((step >> 8U) & 0xFFU),
                    };
                    const cy_bytes_t msg = { .size = payload.size(), .data = payload.data(), .next = nullptr };
                    (void)cy_publish(pub, platform.now + 50'000, msg);
                }
                break;
            }
            case 5: { // publish reliable
                if (pub != nullptr) {
                    const std::array<unsigned char, 3> payload = { 0xA1U, 0xB2U, 0xC3U };
                    const cy_bytes_t   msg = { .size = payload.size(), .data = payload.data(), .next = nullptr };
                    cy_future_t* const fut = cy_publish_reliable(pub, platform.now + 80'000, msg);
                    if (fut != nullptr) {
                        futures.push_back(future_entry_t{ .fut = fut, .pub_slot = slot });
                    }
                }
                break;
            }
            case 6: { // request
                if (pub != nullptr) {
                    const std::array<unsigned char, 3> payload = { 0x11U, 0x22U, 0x33U };
                    const cy_bytes_t   msg = { .size = payload.size(), .data = payload.data(), .next = nullptr };
                    cy_future_t* const fut = cy_request(pub, platform.now + 80'000, 60'000, msg);
                    if (fut != nullptr) {
                        futures.push_back(future_entry_t{ .fut = fut, .pub_slot = slot });
                    }
                }
                break;
            }
            case 7: { // mutate publisher QoS knobs
                if (pub != nullptr) {
                    const auto priority_raw = static_cast<std::uint8_t>(rng_mod(rng, 16U));
                    auto       priority     = cy_prio_t{};
                    std::memcpy(&priority, &priority_raw, sizeof(priority_raw));
                    cy_priority_set(pub, priority);
                    const auto ack_timeout = static_cast<cy_us_t>(1U) + static_cast<cy_us_t>(rng_mod(rng, 100'000U));
                    cy_ack_timeout_set(pub, ack_timeout);
                }
                break;
            }
            case 8: { // collect done futures
                for (std::ptrdiff_t i = static_cast<std::ptrdiff_t>(futures.size()) - 1; i >= 0; i--) {
                    const auto ix = static_cast<std::size_t>(i);
                    if ((futures.at(ix).fut == nullptr) || cy_future_done(futures.at(ix).fut)) {
                        destroy_future_entry(futures, ix);
                    }
                }
                break;
            }
            case 9: {
                (void)cy_spin_once(platform.cy);
                break;
            }
            case 10: {
                const auto step_us = static_cast<cy_us_t>(1U) + static_cast<cy_us_t>(rng_mod(rng, 20'000U));
                (void)cy_spin_until(platform.cy, platform.now + step_us);
                break;
            }
            case 11: { // subscriber timeout mutate
                const auto sub_slot = rng_mod(rng, subscribers.size());
                if (subscribers.at(sub_slot) != nullptr) {
                    const auto timeout_value = static_cast<cy_us_t>(1U) + static_cast<cy_us_t>(rng_mod(rng, 50'000U));
                    const auto timeout       = rng_mod(rng, 2U) == 0U ? cy_us_t{ 0U } : timeout_value;
                    cy_subscriber_timeout_set(subscribers.at(sub_slot), timeout);
                }
                break;
            }
            default: {
                TEST_FAIL_MESSAGE("Unexpected operation selector");
                break;
            }
        }

        TEST_ASSERT_TRUE(cy_test_message_live_count() <= 8U);
    }

    for (std::ptrdiff_t i = static_cast<std::ptrdiff_t>(futures.size()) - 1; i >= 0; i--) {
        destroy_future_entry(futures, static_cast<std::size_t>(i));
    }
    TEST_ASSERT_TRUE(futures.empty());

    for (cy_future_t*& sub : subscribers) {
        if (sub != nullptr) {
            cy_future_destroy(sub);
            sub = nullptr;
        }
    }
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));

    for (cy_publisher_t*& pub : publishers) {
        if (pub != nullptr) {
            cy_unadvertise(pub);
            pub = nullptr;
        }
    }
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
    RUN_TEST(test_api_state_machine_fuzz_lifecycle);
    return UNITY_END();
}
