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

namespace {
constexpr std::uint8_t header_msg_be = 0U;
constexpr std::uint8_t header_gossip = 8U;
constexpr std::size_t  header_bytes  = 24U;

struct send_capture_t
{
    bool                           unicast{ false };
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
    std::size_t                    unicast_send_count{ 0U };
    std::size_t                    capture_count{ 0U };
    std::array<send_capture_t, 64> captures{};
};

test_platform_t* platform_from(cy_platform_t* const platform)
{
    return api_test::platform_from<test_platform_t>(platform);
}

const test_platform_t* platform_from_const(const cy_platform_t* const platform)
{
    return api_test::platform_from_const<test_platform_t>(platform);
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
                  const bool             unicast,
                  const std::uint32_t    subject_id,
                  const std::uint64_t    lane_id,
                  const cy_bytes_t       message)
{
    if (self->capture_count >= self->captures.size()) {
        return;
    }
    send_capture_t& out = self->captures.at(self->capture_count++);
    out                 = send_capture_t{};
    out.unicast         = unicast;
    out.subject_id      = subject_id;
    out.lane_id         = lane_id;
    out.size            = flatten_fragments(message, out.data.data(), out.data.size());
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
    (void)deadline;
    test_platform_t* const self = platform_from(platform);
    self->unicast_send_count++;
    capture_send(self, true, 0U, (lane != nullptr) ? lane->id : 0U, message);
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

extern "C" cy_us_t platform_now(cy_platform_t* const platform) { return platform_from_const(platform)->now; }

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
    self.vtable.unicast                = platform_unicast_send;
    self.vtable.unicast_extent_set     = platform_unicast_extent_set;
    self.vtable.spin                   = platform_spin;
    self.vtable.now                    = platform_now;
    self.vtable.realloc                = platform_realloc;
    self.vtable.random                 = platform_random;
    api_test::init_platform_base(self.platform, self.vtable);
    self.cy = cy_new(&self.platform);
    TEST_ASSERT_NOT_NULL(self.cy);
    cy_async_error_handler_set(self.cy, platform_on_async_error);
}

void platform_deinit(test_platform_t& self)
{
    if (self.cy != nullptr) {
        cy_destroy(self.cy);
        self.cy = nullptr;
    }
    api_test::assert_heaps_clean(self.core_heap, self.message_heap);
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

// Scan captured multicast sends (`subject_writer_send`) for a gossip frame matching the requested hash.
bool has_broadcast_gossip_for_hash_since(const test_platform_t& platform,
                                         const std::size_t      capture_start_index,
                                         const std::uint64_t    topic_hash)
{
    const std::size_t start = std::min(capture_start_index, platform.capture_count);
    for (std::size_t i = start; i < platform.capture_count; i++) {
        const send_capture_t& cap = platform.captures.at(i);
        if (cap.unicast || (cap.size < header_bytes) || (capture_type(cap) != header_gossip)) {
            continue;
        }
        if (capture_u64(cap, 8U) == topic_hash) {
            return true;
        }
    }
    return false;
}

void spin_for(test_platform_t& platform, const cy_us_t duration, const cy_us_t step = 1000)
{
    const cy_us_t start = platform.now;
    while ((platform.now - start) <= duration) {
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
        platform.now += step;
    }
}

bool spin_until_multicast_for_hash(test_platform_t&    platform,
                                   const std::uint64_t topic_hash,
                                   const cy_us_t       duration,
                                   const cy_us_t       step = 1000)
{
    const std::size_t start = platform.capture_count;
    const cy_us_t     t0    = platform.now;
    while ((platform.now - t0) <= duration) {
        TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(platform.cy));
        if (has_broadcast_gossip_for_hash_since(platform, start, topic_hash)) {
            return true;
        }
        platform.now += step;
    }
    return false;
}

void test_api_collision_win_triggers_urgent_multicast()
{
    test_platform_t p{};
    platform_init(p);

    static const char* const local_topic_name = "api/gossip/urgent/collision/local/#1000000000001200";
    cy_publisher_t* const    pub              = cy_advertise(p.cy, cy_str(local_topic_name));
    TEST_ASSERT_NOT_NULL(pub);

    const cy_topic_t* const local_topic = cy_topic_find_by_name(p.cy, cy_str(local_topic_name));
    TEST_ASSERT_NOT_NULL(local_topic);
    const std::uint64_t local_hash = cy_topic_hash(local_topic);

    p.now = 30'000'000;
    spin_for(p, 50'000); // drain startup urgent gossip from topic promotion
    p.capture_count      = 0U;
    p.unicast_send_count = 0U;
    p.subject_send_count = 0U;

    const std::uint64_t remote_colliding_hash = local_hash + static_cast<std::uint64_t>(CY_SUBJECT_ID_MODULUS_17bit);
    dispatch_gossip(p,
                    cy_lane_t{ .id = 203U, .ctx = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    4U,
                    -1,
                    remote_colliding_hash,
                    0U,
                    "api/gossip/urgent/collision/remote",
                    p.now);

    TEST_ASSERT_TRUE(spin_until_multicast_for_hash(p, local_hash, 100'000));
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);

    cy_unadvertise(pub);
    platform_deinit(p);
}

void test_api_arbitration_win_triggers_urgent_multicast()
{
    test_platform_t p{};
    platform_init(p);

    static const char* const local_topic_name = "api/gossip/urgent/arbitration/local/#1000000000001300";
    cy_publisher_t* const    pub              = cy_advertise(p.cy, cy_str(local_topic_name));
    TEST_ASSERT_NOT_NULL(pub);

    const cy_topic_t* const local_topic = cy_topic_find_by_name(p.cy, cy_str(local_topic_name));
    TEST_ASSERT_NOT_NULL(local_topic);
    const std::uint64_t local_hash = cy_topic_hash(local_topic);

    p.now = 31'000'000;
    spin_for(p, 50'000);
    p.capture_count      = 0U;
    p.unicast_send_count = 0U;
    p.subject_send_count = 0U;

    dispatch_gossip(p,
                    cy_lane_t{ .id = 204U, .ctx = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    0U,
                    -1,
                    local_hash,
                    1U,
                    "api/gossip/urgent/arbitration/remote",
                    p.now);

    TEST_ASSERT_TRUE(spin_until_multicast_for_hash(p, local_hash, 100'000));
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);

    cy_unadvertise(pub);
    platform_deinit(p);
}

void test_api_known_topic_local_loss_does_not_emit_urgent_when_subject_unchanged()
{
    test_platform_t p{};
    platform_init(p);

    static const char* const local_topic_name = "api/gossip/known/loss/no-urgent/#1000000000001400";
    cy_publisher_t* const    pub              = cy_advertise(p.cy, cy_str(local_topic_name));
    TEST_ASSERT_NOT_NULL(pub);

    const cy_topic_t* const local_topic = cy_topic_find_by_name(p.cy, cy_str(local_topic_name));
    TEST_ASSERT_NOT_NULL(local_topic);
    const std::uint64_t local_hash = cy_topic_hash(local_topic);

    p.now = 32'000'000;
    spin_for(p, 50'000);
    p.capture_count      = 0U;
    p.unicast_send_count = 0U;
    p.subject_send_count = 0U;

    dispatch_gossip(p,
                    cy_lane_t{ .id = 211U, .ctx = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    4U,
                    20,
                    local_hash,
                    2U,
                    "api/gossip/known/loss/no-urgent/remote",
                    p.now);

    TEST_ASSERT_FALSE(spin_until_multicast_for_hash(p, local_hash, 50'000));
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);

    cy_unadvertise(pub);
    platform_deinit(p);
}

void test_api_unknown_topic_no_collision_and_collision_win_paths()
{
    test_platform_t p{};
    platform_init(p);

    static const char* const local_topic_name = "api/gossip/unknown/matrix/local/#1000000000001600";
    cy_publisher_t* const    pub              = cy_advertise(p.cy, cy_str(local_topic_name));
    TEST_ASSERT_NOT_NULL(pub);

    const cy_topic_t* const local_topic = cy_topic_find_by_name(p.cy, cy_str(local_topic_name));
    TEST_ASSERT_NOT_NULL(local_topic);
    const std::uint64_t local_hash = cy_topic_hash(local_topic);

    p.now = 33'000'000;
    spin_for(p, 50'000);
    p.capture_count      = 0U;
    p.unicast_send_count = 0U;
    p.subject_send_count = 0U;

    const std::uint64_t no_collision_hash = UINT64_C(1234);
    dispatch_gossip(p,
                    cy_lane_t{ .id = 215U, .ctx = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    4U,
                    0,
                    no_collision_hash,
                    0U,
                    "api/gossip/unknown/matrix/no-collision",
                    p.now);
    TEST_ASSERT_FALSE(spin_until_multicast_for_hash(p, no_collision_hash, 50'000));
    TEST_ASSERT_NULL(cy_topic_find_by_hash(p.cy, no_collision_hash));

    const std::uint64_t colliding_hash = local_hash + static_cast<std::uint64_t>(CY_SUBJECT_ID_MODULUS_17bit);
    dispatch_gossip(p,
                    cy_lane_t{ .id = 216U, .ctx = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    4U,
                    -1,
                    colliding_hash,
                    0U,
                    "api/gossip/unknown/matrix/win",
                    p.now);
    TEST_ASSERT_TRUE(spin_until_multicast_for_hash(p, local_hash, 100'000));

    cy_unadvertise(pub);
    platform_deinit(p);
}

void test_api_gossip_parser_rejects_incompatibility_invalid_lage_and_short_header()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 2U, .ctx = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_scout(p, lane, 1U, "api/gossip/>", 101);
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);

    dispatch_gossip(p, lane, nullptr, 1U, static_cast<std::int8_t>(127), UINT64_C(0x1234), 0U, "x/y", 102);
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);

    std::array<unsigned char, 256> wire{};
    const std::size_t              full_size = make_gossip_header(
      wire.data(), wire.size(), 1U, 0, UINT64_C(0x1000000000000002), 0U, cy_str("api/gossip/truncated"));
    TEST_ASSERT_TRUE(full_size > 0U);
    dispatch_raw(p, wire, header_bytes - 6U, lane, nullptr, 103); // header itself is truncated
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);
    platform_deinit(p);
}

void test_api_gossip_parser_rejects_payload_truncated_and_overlong_name_length()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 24U, .ctx = { { 0 } }, .prio = cy_prio_nominal };

    std::array<unsigned char, 256> wire{};
    const std::size_t              full_size = make_gossip_header(
      wire.data(), wire.size(), 1U, 0, UINT64_C(0x1000000000000004), 0U, cy_str("api/gossip/truncated"));
    TEST_ASSERT_TRUE(full_size > 0U);
    dispatch_raw(p, wire, header_bytes, lane, nullptr, 110); // header complete, payload omitted
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);

    std::array<unsigned char, 256> wire_overlong = wire;
    wire_overlong[header_bytes - 1U]             = static_cast<unsigned char>(CY_TOPIC_NAME_MAX + 1U);
    dispatch_raw(p, wire_overlong, full_size, lane, nullptr, 111);
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);
    platform_deinit(p);
}

void test_api_gossip_parser_rejects_gossip_incompatibility_u32()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 21U, .ctx = { { 0 } }, .prio = cy_prio_nominal };

    std::array<unsigned char, 256> wire{};
    const std::size_t              full_size =
      make_gossip_header(wire.data(), wire.size(), 1U, 0, UINT64_C(0x1000000000000033), 0U, cy_str("api/gossip/inc"));
    TEST_ASSERT_TRUE(full_size > 0U);
    wire[4] = 1U; // incompatibility in little-endian u32 field at [4..7]
    dispatch_raw(p, wire, full_size, lane, nullptr, 104);
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, p.subject_send_count);
    platform_deinit(p);
}

void test_api_gossip_parser_rejects_pinned_hash_with_nonzero_evictions()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 22U, .ctx = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_gossip(p, lane, nullptr, 1U, 0, UINT64_C(1234), 1U, "api/gossip/pinned/reject", 105);
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(p.cy, UINT64_C(1234)));
    platform_deinit(p);
}

void test_api_scout_parser_rejects_empty_and_truncated_pattern()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();
    const cy_lane_t lane = { .id = 23U, .ctx = { { 0 } }, .prio = cy_prio_nominal };

    dispatch_scout(p, lane, 0U, "", 106);
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);

    std::array<unsigned char, 256> wire{};
    const std::size_t              full_size = make_scout_header(wire.data(), wire.size(), 0U, cy_str("abc"));
    TEST_ASSERT_TRUE(full_size > 0U);
    dispatch_raw(p, wire, header_bytes + 1U, lane, nullptr, 107);
    wire[header_bytes - 1U] = static_cast<unsigned char>(CY_TOPIC_NAME_MAX + 1U);
    dispatch_raw(p, wire, full_size, lane, nullptr, 108);

    std::array<unsigned char, 256> wire_reserved = wire;
    wire_reserved[header_bytes - 1U]             = 3U; // valid small length
    wire_reserved[8U]                            = 1U; // reserved u64 field must be zero
    dispatch_raw(p, wire_reserved, full_size, lane, nullptr, 109);

    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, p.subject_send_count);
    platform_deinit(p);
}

void test_api_gossip_invalid_frame_has_no_side_effects()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();

    const cy_subject_reader_t broad_reader = { .subject_id = cy_broadcast_subject_id(&p.platform) };
    dispatch_gossip(p,
                    cy_lane_t{ .id = 31U, .ctx = { { 0 } }, .prio = cy_prio_nominal },
                    &broad_reader,
                    1U,
                    0,
                    UINT64_C(0x1000000000000044),
                    0U,
                    "api/gossip/invalid/nopeer",
                    108);

    dispatch_gossip(p,
                    cy_lane_t{ .id = 32U, .ctx = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    3U,
                    0,
                    UINT64_C(0x1000000000000045),
                    0U,
                    "api/gossip/valid/nopeer",
                    109);
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);
    platform_deinit(p);
}

void test_api_message_with_reader_above_sid_max_treated_as_nonmulticast()
{
    test_platform_t p{};
    platform_init(p);
    cy_test_message_reset_counters();

    const std::uint64_t            hash = UINT64_C(0x1000000000000046);
    std::array<unsigned char, 256> wire{};
    make_message_header(wire.data(), header_msg_be, UINT64_C(0xA5A5), hash);

    const cy_subject_reader_t out_of_range_reader = {
        .subject_id = CY_SUBJECT_ID_MAX(p.platform.subject_id_modulus) + 1U,
    };
    dispatch_raw(p,
                 wire,
                 header_bytes,
                 cy_lane_t{ .id = 33U, .ctx = { { 0 } }, .prio = cy_prio_nominal },
                 &out_of_range_reader,
                 112);

    TEST_ASSERT_EQUAL_size_t(0U, p.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, p.unicast_send_count);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(p.cy, hash));
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
    p.unicast_send_count = 0U;
    p.capture_count      = 0U;

    dispatch_scout(p, cy_lane_t{ .id = 99U, .ctx = { { 0 } }, .prio = cy_prio_fast }, 0U, "api/gossip/scout/>", 200);
    TEST_ASSERT_TRUE(p.unicast_send_count > 0U);
    const send_capture_t& c = p.captures.at(p.capture_count - 1U);
    TEST_ASSERT_TRUE(c.unicast);
    TEST_ASSERT_EQUAL_UINT8(header_gossip, capture_type(c));
    TEST_ASSERT_EQUAL_UINT64(cy_topic_hash(topic), capture_u64(c, 8U));
    TEST_ASSERT_EQUAL_UINT8(0U, c.data[2]); // scout response TTL is zero

    cy_unadvertise(pub);
    platform_deinit(p);
}

void test_api_scout_match_always_uses_unicast()
{
    test_platform_t p{};
    platform_init(p);
    cy_publisher_t* const pub = cy_advertise(p.cy, cy_str("api/gossip/broadcast/soon"));
    TEST_ASSERT_NOT_NULL(pub);
    p.now                               = 1000;
    static const unsigned char msg_byte = 0x42U;
    const cy_bytes_t           msg      = { .size = 1U, .data = &msg_byte, .next = nullptr };
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_publish(pub, p.now + 1000, msg));
    p.unicast_send_count = 0U;
    p.capture_count      = 0U;

    dispatch_scout(
      p, cy_lane_t{ .id = 77U, .ctx = { { 0 } }, .prio = cy_prio_nominal }, 0U, "api/gossip/broadcast/>", p.now);
    TEST_ASSERT_TRUE(p.unicast_send_count > 0U);

    cy_unadvertise(pub);
    platform_deinit(p);
}

void test_api_unknown_topic_no_pattern_does_not_autocreate()
{
    test_platform_t p{};
    platform_init(p);

    // Unknown topic and no pattern subscriber => no implicit topic creation.
    dispatch_gossip(p,
                    cy_lane_t{ .id = 14U, .ctx = { { 0 } }, .prio = cy_prio_nominal },
                    nullptr,
                    1U,
                    0,
                    UINT64_C(0x10000000000ABC00),
                    0U,
                    "api/gossip/unknown/topic",
                    305);
    TEST_ASSERT_NULL(cy_topic_find_by_hash(p.cy, UINT64_C(0x10000000000ABC00)));

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
    RUN_TEST(test_api_collision_win_triggers_urgent_multicast);
    RUN_TEST(test_api_arbitration_win_triggers_urgent_multicast);
    RUN_TEST(test_api_known_topic_local_loss_does_not_emit_urgent_when_subject_unchanged);
    RUN_TEST(test_api_unknown_topic_no_collision_and_collision_win_paths);
    RUN_TEST(test_api_gossip_parser_rejects_incompatibility_invalid_lage_and_short_header);
    RUN_TEST(test_api_gossip_parser_rejects_payload_truncated_and_overlong_name_length);
    RUN_TEST(test_api_gossip_parser_rejects_gossip_incompatibility_u32);
    RUN_TEST(test_api_gossip_parser_rejects_pinned_hash_with_nonzero_evictions);
    RUN_TEST(test_api_scout_parser_rejects_empty_and_truncated_pattern);
    RUN_TEST(test_api_gossip_invalid_frame_has_no_side_effects);
    RUN_TEST(test_api_message_with_reader_above_sid_max_treated_as_nonmulticast);
    RUN_TEST(test_api_scout_match_triggers_gossip_response_and_fields_are_correct);
    RUN_TEST(test_api_scout_match_always_uses_unicast);
    RUN_TEST(test_api_unknown_topic_no_pattern_does_not_autocreate);
    return UNITY_END();
}
