#include <cy_platform.h>
#include <unity.h>
#include "guarded_heap.h"
#include "helpers.h"
#include "message.h"
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>

namespace {
constexpr std::uint8_t header_gossip = 7U;
constexpr std::size_t  header_bytes  = 24U;

struct test_subject_writer_t
{
    cy_subject_writer_t base{};
};

struct test_subject_reader_t
{
    cy_subject_reader_t base{};
    std::size_t         extent{ 0U };
};

struct send_capture_t
{
    bool                           p2p{ false };
    std::uint32_t                  subject_id{ 0U };
    std::uint64_t                  lane_id{ 0U };
    std::size_t                    size{ 0U };
    std::array<unsigned char, 256> data{};
};

struct test_platform_t final
{
    cy_platform_t        platform{};
    cy_platform_vtable_t vtable{};
    guarded_heap_t       core_heap{};
    guarded_heap_t       message_heap{};

    cy_t*         cy{ nullptr };
    cy_us_t       now{ 0 };
    std::uint64_t random_state{ UINT64_C(0x123456789ABCDEF0) };

    std::size_t                    subject_send_count{ 0U };
    std::size_t                    p2p_send_count{ 0U };
    std::size_t                    capture_count{ 0U };
    std::array<send_capture_t, 64> captures{};
};

test_platform_t* platform_from(cy_platform_t* const platform)
{
    return reinterpret_cast<test_platform_t*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

const test_platform_t* platform_from_const(const cy_platform_t* const platform)
{
    return reinterpret_cast<const test_platform_t*>(platform); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast)
}

std::size_t flatten_fragments(const cy_bytes_t message, unsigned char* const out, const std::size_t out_size)
{
    std::size_t       copied = 0U;
    const cy_bytes_t* frag   = &message;
    while ((frag != nullptr) && (copied < out_size)) {
        if ((frag->size > 0U) && (frag->data != nullptr)) {
            const std::size_t n = ((out_size - copied) < frag->size) ? (out_size - copied) : frag->size;
            std::memcpy(out + copied, frag->data, n);
            copied += n;
        }
        frag = frag->next;
    }
    return copied;
}

void capture_send(test_platform_t* const self,
                  const bool             p2p,
                  const std::uint32_t    subject_id,
                  const std::uint64_t    lane_id,
                  const cy_bytes_t       message)
{
    if (self->capture_count >= self->captures.size()) {
        return;
    }
    send_capture_t& out = self->captures.at(self->capture_count++);
    out                 = send_capture_t{};
    out.p2p             = p2p;
    out.subject_id      = subject_id;
    out.lane_id         = lane_id;
    out.size            = flatten_fragments(message, out.data.data(), out.data.size());
}

extern "C" cy_subject_writer_t* platform_subject_writer_new(cy_platform_t* const platform,
                                                            const std::uint32_t  subject_id)
{
    test_platform_t* const self = platform_from(platform);
    auto* const            out =
      static_cast<test_subject_writer_t*>(guarded_heap_alloc(&self->core_heap, sizeof(test_subject_writer_t)));
    if (out != nullptr) {
        out->base.subject_id = subject_id;
    }
    return (out != nullptr) ? &out->base : nullptr;
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
    self->subject_send_count++;
    capture_send(self, false, (writer != nullptr) ? writer->subject_id : 0U, 0U, message);
    return CY_OK;
}

extern "C" cy_subject_reader_t* platform_subject_reader_new(cy_platform_t* const platform,
                                                            const std::uint32_t  subject_id,
                                                            const std::size_t    extent)
{
    test_platform_t* const self = platform_from(platform);
    auto* const            out =
      static_cast<test_subject_reader_t*>(guarded_heap_alloc(&self->core_heap, sizeof(test_subject_reader_t)));
    if (out != nullptr) {
        out->base.subject_id = subject_id;
        out->extent          = extent;
    }
    return (out != nullptr) ? &out->base : nullptr;
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
    (void)deadline;
    test_platform_t* const self = platform_from(platform);
    self->p2p_send_count++;
    capture_send(self, true, 0U, (lane != nullptr) ? lane->id : 0U, message);
    return CY_OK;
}

extern "C" void platform_p2p_extent_set(cy_platform_t* const platform, const std::size_t extent)
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

extern "C" cy_us_t platform_now(cy_platform_t* const platform) { return platform_from_const(platform)->now; }

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
    (void)error;
    (void)line_number;
}

void platform_init(test_platform_t& self)
{
    self = test_platform_t{};
    guarded_heap_init(&self.core_heap, UINT64_C(0xAAAABBBBCCCCDDDD));
    guarded_heap_init(&self.message_heap, UINT64_C(0x1111222233334444));

    self.vtable.subject_writer_new     = platform_subject_writer_new;
    self.vtable.subject_writer_destroy = platform_subject_writer_destroy;
    self.vtable.subject_writer_send    = platform_subject_writer_send;
    self.vtable.subject_reader_new     = platform_subject_reader_new;
    self.vtable.subject_reader_destroy = platform_subject_reader_destroy;
    self.vtable.p2p_send               = platform_p2p_send;
    self.vtable.p2p_extent_set         = platform_p2p_extent_set;
    self.vtable.spin                   = platform_spin;
    self.vtable.now                    = platform_now;
    self.vtable.realloc                = platform_realloc;
    self.vtable.random                 = platform_random;
    self.platform.subject_id_modulus   = static_cast<std::uint32_t>(CY_SUBJECT_ID_MODULUS_17bit);
    self.platform.vtable               = &self.vtable;
    self.cy                            = cy_new(&self.platform);
    TEST_ASSERT_NOT_NULL(self.cy);
    cy_async_error_handler_set(self.cy, platform_on_async_error);
}

void platform_deinit(test_platform_t& self)
{
    if (self.cy != nullptr) {
        cy_destroy(self.cy);
        self.cy = nullptr;
    }
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self.message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self.message_heap));
}

void dispatch_raw(test_platform_t&                      platform,
                  const std::array<unsigned char, 256>& wire,
                  const std::size_t                     size,
                  const cy_lane_t&                      lane,
                  const cy_subject_reader_t* const      reader,
                  const cy_us_t                         ts)
{
    cy_message_t* const msg = cy_test_message_make(&platform.message_heap, wire.data(), size);
    TEST_ASSERT_NOT_NULL(msg);
    cy_message_ts_t mts{};
    mts.timestamp = ts;
    mts.content   = msg;
    cy_on_message(&platform.platform, lane, reader, mts);
}

void dispatch_gossip(test_platform_t&           platform,
                     const cy_lane_t&           lane,
                     const cy_subject_reader_t* reader,
                     const std::uint8_t         ttl,
                     const std::int8_t          lage,
                     const std::uint64_t        hash,
                     const std::uint32_t        evictions,
                     const char* const          name,
                     const cy_us_t              ts)
{
    std::array<unsigned char, 256> wire{};
    const std::size_t size = make_gossip_header(wire.data(), wire.size(), ttl, lage, hash, evictions, cy_str(name));
    TEST_ASSERT_TRUE(size > 0U);
    dispatch_raw(platform, wire, size, lane, reader, ts);
}

void dispatch_scout(test_platform_t&    platform,
                    const cy_lane_t&    lane,
                    const std::uint64_t incompatibility,
                    const char* const   pattern,
                    const cy_us_t       ts)
{
    std::array<unsigned char, 256> wire{};
    const std::size_t              size = make_scout_header(wire.data(), wire.size(), incompatibility, cy_str(pattern));
    TEST_ASSERT_TRUE(size > 0U);
    dispatch_raw(platform, wire, size, lane, nullptr, ts);
}

std::uint8_t capture_type(const send_capture_t& c)
{
    return (c.size > 0U) ? static_cast<std::uint8_t>(c.data[0] & 63U) : 0xFFU;
}

std::uint64_t capture_u64(const send_capture_t& c, const std::size_t off)
{
    std::uint64_t out = 0U;
    for (std::size_t i = 0U; i < 8U; i++) {
        out |= static_cast<std::uint64_t>(c.data.at(off + i)) << (i * 8U);
    }
    return out;
}

void test_api_gossip_parser_rejects_broadcast_nonzero_ttl()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();

    const cy_subject_reader_t broad_reader = { .subject_id = cy_broadcast_subject_id(&p.platform) };
    dispatch_gossip(p,
                    cy_lane_t{ .id = 1U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
                    &broad_reader,
                    1U,
                    0,
                    UINT64_C(0x1000000000000001),
                    0U,
                    "api/gossip/ttl",
                    100);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, p.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(1U, cy_test_message_destroy_count());
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
    platform_deinit(p);
}

void test_api_gossip_parser_rejects_incompatibility_invalid_lage_and_short_header()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 2U, .p2p = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_scout(p, lane, 1U, "api/gossip/>", 101);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);

    dispatch_gossip(p, lane, nullptr, 1U, static_cast<std::int8_t>(127), UINT64_C(0x1234), 0U, "x/y", 102);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);

    std::array<unsigned char, 256> wire{};
    const std::size_t              full_size = make_gossip_header(
      wire.data(), wire.size(), 1U, 0, UINT64_C(0x1000000000000002), 0U, cy_str("api/gossip/truncated"));
    TEST_ASSERT_TRUE(full_size > 0U);
    dispatch_raw(p, wire, header_bytes - 6U, lane, nullptr, 103); // header itself is truncated
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);
    platform_deinit(p);
}

void test_api_gossip_parser_rejects_payload_truncated_and_overlong_name_length()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 24U, .p2p = { { 0 } }, .prio = cy_prio_nominal };

    std::array<unsigned char, 256> wire{};
    const std::size_t              full_size = make_gossip_header(
      wire.data(), wire.size(), 1U, 0, UINT64_C(0x1000000000000004), 0U, cy_str("api/gossip/truncated"));
    TEST_ASSERT_TRUE(full_size > 0U);
    dispatch_raw(p, wire, header_bytes, lane, nullptr, 110); // header complete, payload omitted
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);

    std::array<unsigned char, 256> wire_overlong = wire;
    wire_overlong[header_bytes - 1U]             = static_cast<unsigned char>(CY_TOPIC_NAME_MAX + 1U);
    dispatch_raw(p, wire_overlong, full_size, lane, nullptr, 111);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);
    platform_deinit(p);
}

void test_api_gossip_parser_rejects_gossip_incompatibility_u32()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 21U, .p2p = { { 0 } }, .prio = cy_prio_nominal };

    std::array<unsigned char, 256> wire{};
    const std::size_t              full_size =
      make_gossip_header(wire.data(), wire.size(), 1U, 0, UINT64_C(0x1000000000000033), 0U, cy_str("api/gossip/inc"));
    TEST_ASSERT_TRUE(full_size > 0U);
    wire[4] = 1U; // incompatibility in little-endian u32 field at [4..7]
    dispatch_raw(p, wire, full_size, lane, nullptr, 104);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, p.subject_send_count);
    platform_deinit(p);
}

void test_api_gossip_parser_rejects_pinned_hash_with_nonzero_evictions()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 22U, .p2p = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_gossip(p, lane, nullptr, 1U, 0, UINT64_C(1234), 1U, "api/gossip/pinned/reject", 105);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(p.cy, UINT64_C(1234)));
    platform_deinit(p);
}

void test_api_scout_parser_rejects_empty_and_truncated_pattern()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 23U, .p2p = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_scout(p, lane, 0U, "", 106);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);

    std::array<unsigned char, 256> wire{};
    const std::size_t              full_size = make_scout_header(wire.data(), wire.size(), 0U, cy_str("abc"));
    TEST_ASSERT_TRUE(full_size > 0U);
    dispatch_raw(p, wire, header_bytes + 1U, lane, nullptr, 107);
    wire[header_bytes - 1U] = static_cast<unsigned char>(CY_TOPIC_NAME_MAX + 1U);
    dispatch_raw(p, wire, full_size, lane, nullptr, 108);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, p.subject_send_count);
    platform_deinit(p);
}

void test_api_gossip_invalid_frame_does_not_seed_peer_sampler()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();

    const cy_subject_reader_t broad_reader = { .subject_id = cy_broadcast_subject_id(&p.platform) };
    dispatch_gossip(p,
                    cy_lane_t{ .id = 31U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
                    &broad_reader,
                    1U,
                    0,
                    UINT64_C(0x1000000000000044),
                    0U,
                    "api/gossip/invalid/nopeer",
                    108);

    dispatch_gossip(p,
                    cy_lane_t{ .id = 32U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    3U,
                    0,
                    UINT64_C(0x1000000000000045),
                    0U,
                    "api/gossip/valid/nopeer",
                    109);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);
    platform_deinit(p);
}

void test_api_scout_match_triggers_gossip_response_and_fields_are_correct()
{
    test_platform_t p{};
    platform_init(p);
    cy_publisher_t* const pub = cy_advertise(p.cy, cy_str("api/gossip/scout/topic"));
    TEST_ASSERT_NOT_NULL(pub);
    const cy_topic_t* const topic = cy_topic_find_by_name(p.cy, cy_str("api/gossip/scout/topic"));
    TEST_ASSERT_NOT_NULL(topic);

    // Run two spins: first starts gossip scheduling, second emits a broadcast and
    // pushes the next broadcast into the future, so scout should answer via unicast.
    p.now = 0;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(p.cy));
    p.now = 1;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(p.cy));
    p.subject_send_count = 0U;
    p.p2p_send_count     = 0U;
    p.capture_count      = 0U;

    dispatch_scout(p, cy_lane_t{ .id = 99U, .p2p = { { 0 } }, .prio = cy_prio_fast }, 0U, "api/gossip/scout/>", 200);
    TEST_ASSERT_TRUE(p.p2p_send_count > 0U);
    const send_capture_t& c = p.captures.at(p.capture_count - 1U);
    TEST_ASSERT_TRUE(c.p2p);
    TEST_ASSERT_EQUAL_UINT8(header_gossip, capture_type(c));
    TEST_ASSERT_EQUAL_UINT64(cy_topic_hash(topic), capture_u64(c, 8U));
    TEST_ASSERT_EQUAL_UINT8(0U, c.data[2]); // scout response TTL is zero

    cy_unadvertise(pub);
    platform_deinit(p);
}

void test_api_scout_broadcast_soon_optimization_suppresses_unicast()
{
    test_platform_t p{};
    platform_init(p);
    cy_publisher_t* const pub = cy_advertise(p.cy, cy_str("api/gossip/broadcast/soon"));
    TEST_ASSERT_NOT_NULL(pub);
    p.now                               = 1000;
    static const unsigned char msg_byte = 0x42U;
    const cy_bytes_t           msg      = { .size = 1U, .data = &msg_byte, .next = nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, p.now + 1000, msg));
    p.p2p_send_count = 0U;
    p.capture_count  = 0U;

    dispatch_scout(
      p, cy_lane_t{ .id = 77U, .p2p = { { 0 } }, .prio = cy_prio_nominal }, 0U, "api/gossip/broadcast/>", p.now);
    TEST_ASSERT_EQUAL_size_t(0U, p.p2p_send_count);

    cy_unadvertise(pub);
    platform_deinit(p);
}

void test_api_repair_smoke_duplicate_suppression_and_unknown_topic_no_autocreate()
{
    test_platform_t p{};
    platform_init(p);
    cy_publisher_t* const pub = cy_advertise(p.cy, cy_str("api/gossip/repair/topic"));
    TEST_ASSERT_NOT_NULL(pub);
    const cy_topic_t* const mine = cy_topic_find_by_name(p.cy, cy_str("api/gossip/repair/topic"));
    TEST_ASSERT_NOT_NULL(mine);

    // Prime peer set.
    dispatch_gossip(p,
                    cy_lane_t{ .id = 10U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    1U,
                    0,
                    UINT64_C(0x1001),
                    0U,
                    "x/1",
                    300);
    dispatch_gossip(p,
                    cy_lane_t{ .id = 11U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    1U,
                    0,
                    UINT64_C(0x1002),
                    0U,
                    "x/2",
                    301);

    // Duplicate suppression smoke on forwarded unknown gossip.
    const std::size_t p2p_before = p.p2p_send_count;
    dispatch_gossip(p,
                    cy_lane_t{ .id = 12U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    3U,
                    0,
                    UINT64_C(0x1003),
                    1U,
                    "x/3",
                    302);
    const std::size_t first_forward = p.p2p_send_count;
    TEST_ASSERT_TRUE(first_forward >= p2p_before);
    dispatch_gossip(p,
                    cy_lane_t{ .id = 12U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    3U,
                    0,
                    UINT64_C(0x1003),
                    1U,
                    "x/3",
                    303);
    TEST_ASSERT_EQUAL_size_t(first_forward, p.p2p_send_count);

    // Local-win divergence schedules urgent gossip; observe unicast repair emission after spins.
    const std::size_t before_repair = p.p2p_send_count;
    dispatch_gossip(p,
                    cy_lane_t{ .id = 13U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    4U,
                    -1,
                    cy_topic_hash(mine),
                    0U,
                    "api/gossip/repair/topic",
                    304);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(p.cy)); // may broadcast first
    p.now += 1;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(p.cy)); // urgent pass
    TEST_ASSERT_TRUE(p.p2p_send_count > before_repair);

    // Unknown topic and no pattern subscriber => no implicit topic creation.
    dispatch_gossip(p,
                    cy_lane_t{ .id = 14U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    1U,
                    0,
                    UINT64_C(0x10000000000ABC00),
                    0U,
                    "api/gossip/unknown/topic",
                    305);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(p.cy, UINT64_C(0x10000000000ABC00)));

    cy_unadvertise(pub);
    platform_deinit(p);
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
    RUN_TEST(test_api_gossip_parser_rejects_broadcast_nonzero_ttl);
    RUN_TEST(test_api_gossip_parser_rejects_incompatibility_invalid_lage_and_short_header);
    RUN_TEST(test_api_gossip_parser_rejects_payload_truncated_and_overlong_name_length);
    RUN_TEST(test_api_gossip_parser_rejects_gossip_incompatibility_u32);
    RUN_TEST(test_api_gossip_parser_rejects_pinned_hash_with_nonzero_evictions);
    RUN_TEST(test_api_scout_parser_rejects_empty_and_truncated_pattern);
    RUN_TEST(test_api_gossip_invalid_frame_does_not_seed_peer_sampler);
    RUN_TEST(test_api_scout_match_triggers_gossip_response_and_fields_are_correct);
    RUN_TEST(test_api_scout_broadcast_soon_optimization_suppresses_unicast);
    RUN_TEST(test_api_repair_smoke_duplicate_suppression_and_unknown_topic_no_autocreate);
    return UNITY_END();
}
