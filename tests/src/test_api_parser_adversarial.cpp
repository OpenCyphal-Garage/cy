#include <cy_platform.h>
#include <unity.h>
#include "api_mock_platform_utils.hpp"
#include "guarded_heap.h"
#include "helpers.h"
#include "message.h"
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <set>
#include <vector>

namespace {

constexpr std::size_t header_bytes = 24U;

struct test_platform_t final
{
    cy_platform_t        platform{};
    cy_platform_vtable_t vtable{};
    guarded_heap_t       core_heap{};
    guarded_heap_t       message_heap{};
    cy_t*                cy{ nullptr };

    cy_us_t       now{ 0 };
    std::uint64_t random_state{ UINT64_C(0xA5A5A5A5A5A5A5A5) };

    std::size_t subject_send_count{ 0U };
    std::size_t unicast_send_count{ 0U };

    std::set<std::uint32_t> active_reader_subjects;
    std::set<std::uint32_t> active_writer_subjects;
};

std::size_t g_async_error_count = 0U; // NOLINT(*-non-const-global-variables)

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
    (void)writer;
    (void)deadline;
    (void)priority;
    (void)message;
    platform_from(platform)->subject_send_count++;
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
    (void)lane;
    (void)deadline;
    (void)message;
    platform_from(platform)->unicast_send_count++;
    return CY_OK;
}

extern "C" void platform_unicast_extent_set(cy_platform_t* const platform, const std::size_t extent)
{
    (void)platform;
    (void)extent;
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

extern "C" void on_async_error(cy_t* const         cy,
                               cy_topic_t* const   topic,
                               const cy_err_t      error,
                               const std::uint16_t line_number)
{
    (void)topic;
    (void)error;
    (void)line_number;
    TEST_ASSERT_NOT_NULL(cy);
    g_async_error_count++;
}

void platform_init(test_platform_t* const self)
{
    *self               = test_platform_t{};
    g_async_error_count = 0U;
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
    cy_async_error_handler_set(self->cy, on_async_error);
}

void platform_deinit(test_platform_t* const self)
{
    if (self->cy != nullptr) {
        cy_destroy(self->cy);
        self->cy = nullptr;
    }
    api_test::assert_heaps_clean(self->core_heap, self->message_heap);
}

void dispatch_raw(test_platform_t* const            self,
                  const std::vector<unsigned char>& wire,
                  const cy_lane_t                   lane,
                  const cy_subject_reader_t* const  reader,
                  const cy_us_t                     timestamp)
{
    cy_message_t* const msg = cy_test_message_make(&self->message_heap, wire.data(), wire.size());
    TEST_ASSERT_NOT_NULL(msg);
    cy_message_ts_t mts{};
    mts.timestamp                         = timestamp;
    mts.content                           = msg;
    const std::uint32_t* const subject_id = (reader != nullptr) ? &reader->subject_id : nullptr;
    cy_on_message(&self->platform, lane, subject_id, mts);
}

std::uint32_t subject_id_for_hash(const std::uint64_t hash, const std::uint32_t evictions, const std::uint32_t modulus)
{
    if (evictions >= (UINT32_MAX - CY_SUBJECT_ID_PINNED_MAX)) { // is_pinned(evictions)
        return static_cast<std::uint32_t>(UINT32_MAX - evictions);
    }
    const std::uint64_t offset =
      (hash + (static_cast<std::uint64_t>(evictions) * static_cast<std::uint64_t>(evictions))) % modulus;
    return CY_SUBJECT_ID_PINNED_MAX + 1U + static_cast<std::uint32_t>(offset);
}

std::vector<std::vector<unsigned char>> build_corpus(const std::uint64_t known_topic_hash)
{
    std::vector<std::vector<unsigned char>> out{};

    // Baseline frames for all currently used header types.
    for (std::uint8_t type = 0U; type <= 7U; type++) {
        std::vector<unsigned char> wire(header_bytes + 2U, 0U);
        make_message_header(wire.data(), type, UINT64_C(0x1122334455667788), known_topic_hash);
        wire[header_bytes + 0U] = 0xA5U;
        wire[header_bytes + 1U] = 0x5AU;
        out.push_back(wire);
    }
    {
        std::vector<unsigned char> wire(256U, 0U);
        const std::size_t          size =
          make_gossip_header(wire.data(), wire.size(), 0U, 0, UINT64_C(0x1000000000000100), 0U, cy_str("fuzz/gossip"));
        wire.resize(size);
        out.push_back(wire);
    }
    {
        std::vector<unsigned char> wire(256U, 0U);
        const std::size_t          size = make_scout_header(wire.data(), wire.size(), 0U, cy_str("fuzz/>"));
        wire.resize(size);
        out.push_back(wire);
    }
    {
        std::vector<unsigned char> wire(header_bytes, 0U);
        wire[0] = 63U; // unknown type
        out.push_back(wire);
    }

    // Deterministic mutations per baseline.
    std::vector<std::vector<unsigned char>> all{};
    for (const std::vector<unsigned char>& base : out) {
        all.push_back(base);

        const std::size_t truncate_max = std::min<std::size_t>(base.size(), header_bytes + 2U);
        for (std::size_t len = 0U; len <= truncate_max; len++) {
            all.emplace_back(base.begin(), base.begin() + static_cast<std::ptrdiff_t>(len));
        }

        const std::array<std::size_t, 10>  positions = { 0U, 1U, 2U, 3U, 4U, 8U, 15U, 16U, 23U, base.size() - 1U };
        const std::array<unsigned char, 3> masks     = { 0x01U, 0x80U, 0xFFU };
        for (const std::size_t pos : positions) {
            if (pos >= base.size()) {
                continue;
            }
            for (const unsigned char mask : masks) {
                std::vector<unsigned char> m = base;
                m[pos] ^= mask;
                all.push_back(m);
            }
        }

        if (!base.empty()) {
            for (std::uint8_t type = 0U; type < 16U; type++) {
                std::vector<unsigned char> m = base;
                m[0]                         = type;
                all.push_back(m);
            }
        }
    }
    return all;
}

void test_api_parser_adversarial_mutation_corpus()
{
    test_platform_t platform{};
    platform_init(&platform);

    // Keep one known topic alive so the parser traverses both known and unknown topic paths.
    cy_publisher_t* const pub = cy_advertise(platform.cy, cy_str("fuzz/topic"));
    TEST_ASSERT_NOT_NULL(pub);
    const cy_topic_t* const topic = cy_publisher_topic(pub);
    TEST_ASSERT_NOT_NULL(topic);
    const std::uint64_t topic_hash = cy_topic_hash(topic);

    const std::vector<std::vector<unsigned char>> corpus = build_corpus(topic_hash);
    TEST_ASSERT_TRUE(!corpus.empty());

    const std::uint32_t       sid        = subject_id_for_hash(topic_hash, 0U, platform.platform.subject_id_modulus);
    const cy_subject_reader_t reader     = { .subject_id = sid, .extent = 0 };
    std::size_t               spin_count = 0U;

    for (std::size_t i = 0U; i < corpus.size(); i++) {
        const cy_lane_t                  lane  = { .id   = static_cast<std::uint64_t>(1000U + i),
                                                   .ctx  = { { 0 } },
                                                   .prio = cy_prio_nominal };
        const cy_subject_reader_t* const route = ((i % 2U) == 0U) ? nullptr : &reader;
        dispatch_raw(&platform, corpus[i], lane, route, static_cast<cy_us_t>(1000) + static_cast<cy_us_t>(i));
        TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
        if ((i % 16U) == 0U) {
            TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
            spin_count++;
        }
    }

    TEST_ASSERT_TRUE(spin_count > 0U);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
    TEST_ASSERT_TRUE(g_async_error_count <= (corpus.size() * 2U));

    cy_unadvertise(pub);
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
    RUN_TEST(test_api_parser_adversarial_mutation_corpus);
    return UNITY_END();
}
