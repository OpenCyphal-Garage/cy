#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include "helpers.h"
#include <string.h>

typedef struct
{
    cy_subject_writer_t base;
} test_subject_writer_t;

typedef struct
{
    cy_subject_reader_t base;
    size_t              extent;
} test_subject_reader_t;

typedef struct
{
    bool          p2p;
    uint32_t      subject_id;
    uint64_t      lane_id;
    size_t        size;
    unsigned char data[HEADER_BYTES + CY_TOPIC_NAME_MAX];
    uint8_t       type;
    uint8_t       ttl;
    int8_t        lage;
    uint64_t      hash;
    uint32_t      evictions;
} send_capture_t;

#define CAPTURE_CAPACITY 64U

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    guarded_heap_t       heap;
    cy_t*                cy;
    cy_us_t              now;

    uint64_t        rand_state;
    const uint64_t* rand_sequence;
    size_t          rand_sequence_size;
    size_t          rand_sequence_index;

    bool fail_subject_send;
    bool fail_p2p_send;

    size_t   subject_send_count;
    size_t   p2p_send_count;
    size_t   subject_reader_destroy_count;
    size_t   subject_writer_destroy_count;
    size_t   async_error_count;
    cy_err_t last_async_error;
    uint16_t last_async_error_line;

    size_t         capture_count;
    send_capture_t capture[CAPTURE_CAPACITY];
} fixture_t;

static fixture_t* fixture_from(cy_platform_t* const platform) { return (fixture_t*)platform; }

static const fixture_t* fixture_from_const(const cy_platform_t* const platform) { return (const fixture_t*)platform; }

static size_t flatten_fragments(const cy_bytes_t message, unsigned char* const out, const size_t out_size)
{
    size_t            copied = 0U;
    const cy_bytes_t* frag   = &message;
    while ((frag != NULL) && (copied < out_size)) {
        if ((frag->size > 0U) && (frag->data != NULL)) {
            const size_t n = smaller(out_size - copied, frag->size);
            memcpy(&out[copied], frag->data, n);
            copied += n;
        }
        frag = frag->next;
    }
    return copied;
}

static void capture_send(fixture_t* const self,
                         const bool       p2p,
                         const uint32_t   subject_id,
                         const uint64_t   lane_id,
                         const cy_bytes_t message)
{
    if (self->capture_count >= CAPTURE_CAPACITY) {
        return;
    }
    send_capture_t* const out = &self->capture[self->capture_count++];
    memset(out, 0, sizeof(*out));
    out->p2p        = p2p;
    out->subject_id = subject_id;
    out->lane_id    = lane_id;
    out->size       = flatten_fragments(message, out->data, sizeof(out->data));
    if (out->size > 0U) {
        out->type = out->data[0];
    }
    if ((out->type == header_gossip) && (out->size >= HEADER_BYTES)) {
        // Gossip wire header layout in cy.c: ttl at byte 2, hash at 8, evictions at 16.
        out->ttl       = out->data[2];
        out->lage      = (int8_t)out->data[3];
        out->hash      = deserialize_u64(&out->data[8]);
        out->evictions = deserialize_u32(&out->data[16]);
    }
}

static cy_us_t fixture_now(cy_platform_t* const platform) { return fixture_from_const(platform)->now; }

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    fixture_t* const self = fixture_from(platform);
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static uint64_t fixture_random(cy_platform_t* const platform)
{
    fixture_t* const self = fixture_from(platform);
    if ((self->rand_sequence != NULL) && (self->rand_sequence_index < self->rand_sequence_size)) {
        return self->rand_sequence[self->rand_sequence_index++];
    }
    self->rand_state = (self->rand_state * UINT64_C(6364136223846793005)) + UINT64_C(1);
    return self->rand_state;
}

static cy_subject_writer_t* fixture_subject_writer_new(cy_platform_t* const platform, const uint32_t subject_id)
{
    fixture_t* const             self = fixture_from(platform);
    test_subject_writer_t* const out  = (test_subject_writer_t*)guarded_heap_alloc(&self->heap, sizeof(*out));
    if (out != NULL) {
        out->base.subject_id = subject_id;
    }
    return (out != NULL) ? &out->base : NULL;
}

static void fixture_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    fixture_t* const self = fixture_from(platform);
    self->subject_writer_destroy_count++;
    guarded_heap_free(&self->heap, writer);
}

static cy_err_t fixture_subject_writer_send(cy_platform_t* const       platform,
                                            cy_subject_writer_t* const writer,
                                            const cy_us_t              deadline,
                                            const cy_prio_t            priority,
                                            const cy_bytes_t           message)
{
    (void)deadline;
    (void)priority;
    fixture_t* const self = fixture_from(platform);
    self->subject_send_count++;
    capture_send(self, false, (writer != NULL) ? writer->subject_id : 0U, 0U, message);
    return self->fail_subject_send ? CY_ERR_MEDIA : CY_OK;
}

static cy_subject_reader_t* fixture_subject_reader_new(cy_platform_t* const platform,
                                                       const uint32_t       subject_id,
                                                       const size_t         extent)
{
    fixture_t* const             self = fixture_from(platform);
    test_subject_reader_t* const out  = (test_subject_reader_t*)guarded_heap_alloc(&self->heap, sizeof(*out));
    if (out != NULL) {
        out->base.subject_id = subject_id;
        out->extent          = extent;
    }
    return (out != NULL) ? &out->base : NULL;
}

static void fixture_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    fixture_t* const self = fixture_from(platform);
    self->subject_reader_destroy_count++;
    guarded_heap_free(&self->heap, reader);
}

static cy_err_t fixture_p2p_send(cy_platform_t* const   platform,
                                 const cy_lane_t* const lane,
                                 const cy_us_t          deadline,
                                 const cy_bytes_t       message)
{
    (void)deadline;
    fixture_t* const self = fixture_from(platform);
    self->p2p_send_count++;
    capture_send(self, true, 0U, (lane != NULL) ? lane->id : 0U, message);
    return self->fail_p2p_send ? CY_ERR_MEDIA : CY_OK;
}

static void fixture_p2p_extent_set(cy_platform_t* const platform, const size_t extent)
{
    (void)platform;
    (void)extent;
}

static cy_err_t fixture_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    (void)platform;
    (void)deadline;
    return CY_OK;
}

static void fixture_on_async_error(cy_t* const cy, cy_topic_t* const topic, const cy_err_t error, const uint16_t line)
{
    (void)topic;
    fixture_t* const self = fixture_from(cy->platform);
    self->async_error_count++;
    self->last_async_error      = error;
    self->last_async_error_line = line;
}

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0x0F0E0D0C0B0A0908));
    self->platform.vtable               = &self->vtable;
    self->platform.subject_id_modulus   = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    self->vtable.subject_writer_new     = fixture_subject_writer_new;
    self->vtable.subject_writer_destroy = fixture_subject_writer_destroy;
    self->vtable.subject_writer_send    = fixture_subject_writer_send;
    self->vtable.subject_reader_new     = fixture_subject_reader_new;
    self->vtable.subject_reader_destroy = fixture_subject_reader_destroy;
    self->vtable.p2p_send               = fixture_p2p_send;
    self->vtable.p2p_extent_set         = fixture_p2p_extent_set;
    self->vtable.spin                   = fixture_spin;
    self->vtable.now                    = fixture_now;
    self->vtable.realloc                = fixture_realloc;
    self->vtable.random                 = fixture_random;
    self->rand_state                    = UINT64_C(0x123456789ABCDEF0);
    self->cy                            = cy_new(&self->platform);
    TEST_ASSERT_NOT_NULL(self->cy);
    cy_async_error_handler_set(self->cy, fixture_on_async_error);
}

static void fixture_deinit(fixture_t* const self)
{
    if (self->cy != NULL) {
        while (self->cy->topics_by_hash != NULL) {
            cy_topic_t* const topic = cy_topic_iter_first(self->cy);
            TEST_ASSERT_NOT_NULL(topic);
            topic->pub_count = 0U;
            topic_destroy(topic);
        }
        if (self->cy->broad_reader != NULL) {
            self->vtable.subject_reader_destroy(&self->platform, self->cy->broad_reader);
            self->cy->broad_reader = NULL;
        }
        if (self->cy->broad_writer != NULL) {
            self->vtable.subject_writer_destroy(&self->platform, self->cy->broad_writer);
            self->cy->broad_writer = NULL;
        }
        mem_free(self->cy, (void*)self->cy->home.str);
        mem_free(self->cy, (void*)self->cy->ns.str);
        self->vtable.realloc(&self->platform, self->cy, 0U);
        self->platform.cy = NULL;
        self->cy          = NULL;
    }
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self->heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self->heap));
}

static void fixture_set_random_sequence(fixture_t* const self, const uint64_t* const seq, const size_t size)
{
    self->rand_sequence       = seq;
    self->rand_sequence_size  = (seq != NULL) ? size : 0U;
    self->rand_sequence_index = 0U;
}

static void fixture_set_now(fixture_t* const self, const cy_us_t now) { self->now = now; }

static cy_lane_t make_lane(const uint64_t id, const uint8_t marker)
{
    cy_lane_t out    = { .id = id, .p2p = { { 0 } }, .prio = cy_prio_nominal };
    out.p2p.state[0] = marker;
    return out;
}

static cy_topic_t* fixture_make_topic(fixture_t* const self, const char* const name, const uint32_t evictions)
{
    cy_topic_t*    out = NULL;
    const cy_str_t nn  = cy_str(name);
    const uint64_t hh  = topic_hash(nn);
    const cy_err_t er  = topic_new(self->cy, &out, nn, hh, evictions, LAGE_MIN);
    TEST_ASSERT_EQUAL_INT(CY_OK, er);
    TEST_ASSERT_NOT_NULL(out);
    return out;
}

static cy_topic_t* fixture_make_explicit_topic(fixture_t* const self, const char* const name, const uint32_t evictions)
{
    cy_topic_t* const out = fixture_make_topic(self, name, evictions);
    out->pub_count        = 1U;
    delist(&self->cy->list_implicit, &out->list_implicit);
    schedule_gossip(out);
    return out;
}

static void fixture_set_peer(fixture_t* const self, const size_t index, const uint64_t id, const cy_us_t last_seen)
{
    TEST_ASSERT(index < GOSSIP_PEER_COUNT);
    self->cy->gossip_peers[index].id        = id;
    self->cy->gossip_peers[index].last_seen = last_seen;
    memset(self->cy->gossip_peers[index].p2p.state, (int)(id & 0xFFU), sizeof(self->cy->gossip_peers[index].p2p.state));
}

static void fixture_on_gossip(fixture_t* const   self,
                              const cy_us_t      ts,
                              const uint_fast8_t ttl,
                              const uint64_t     hash,
                              const uint32_t     evictions,
                              const int_fast8_t  lage,
                              const cy_str_t     name,
                              cy_topic_t** const out_topic,
                              const cy_lane_t    lane)
{
    gossip_peer_update(self->cy, ts, lane);
    on_gossip(self->cy, ts, ttl, hash, evictions, lage, name, out_topic, lane);
}

static size_t dedup_seen_count(const fixture_t* const self)
{
    size_t out = 0U;
    for (size_t i = 0U; i < GOSSIP_DEDUP_CAPACITY; i++) {
        if (self->cy->gossip_dedup[i].last_seen > BIG_BANG) {
            out++;
        }
    }
    return out;
}

static bool dedup_has_hash(const fixture_t* const self, const uint64_t hash)
{
    for (size_t i = 0U; i < GOSSIP_DEDUP_CAPACITY; i++) {
        if (self->cy->gossip_dedup[i].hash == hash) {
            return true;
        }
    }
    return false;
}

static bool dedup_mark(fixture_t* const self, const cy_us_t now, const uint64_t hash)
{
    gossip_dedup_t* const dedup = gossip_dedup_match_or_lru(self->cy, hash);
    const bool            fresh = gossip_dedup_is_fresh(dedup, hash, now);
    gossip_dedup_update(dedup, hash, now);
    return fresh;
}

static bool capture_has_lane(const fixture_t* const self, const uint64_t lane_id)
{
    for (size_t i = 0U; i < self->capture_count; i++) {
        if (self->capture[i].lane_id == lane_id) {
            return true;
        }
    }
    return false;
}

static void test_gossip_dedup_first_duplicate_and_expiry(void)
{
    fixture_t fix;
    fixture_init(&fix);
    fixture_set_now(&fix, 1000);

    const uint64_t h = gossip_dedup_hash(UINT64_C(0x1234567800001111), 3U, 1);
    TEST_ASSERT_TRUE(dedup_mark(&fix, 1000, h));
    TEST_ASSERT_FALSE(dedup_mark(&fix, 1001, h));
    TEST_ASSERT_TRUE(dedup_mark(&fix, 1000 + GOSSIP_DEDUP_TIMEOUT + 2, h));

    fixture_deinit(&fix);
}

static void test_gossip_dedup_expiry_boundary_is_strictly_greater_than_timeout(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const uint64_t h1 = gossip_dedup_hash(UINT64_C(0x1001), 1U, 1);
    TEST_ASSERT_TRUE(dedup_mark(&fix, 10000, h1));
    TEST_ASSERT_FALSE(dedup_mark(&fix, 10000 + GOSSIP_DEDUP_TIMEOUT, h1));

    const uint64_t h2 = gossip_dedup_hash(UINT64_C(0x1002), 2U, 2);
    TEST_ASSERT_TRUE(dedup_mark(&fix, 20000, h2));
    TEST_ASSERT_TRUE(dedup_mark(&fix, 20000 + GOSSIP_DEDUP_TIMEOUT + 1, h2));

    fixture_deinit(&fix);
}

static void test_gossip_dedup_capacity_eviction_replaces_oldest(void)
{
    fixture_t fix;
    fixture_init(&fix);
    for (size_t i = 0U; i < GOSSIP_DEDUP_CAPACITY; i++) {
        TEST_ASSERT_TRUE(dedup_mark(&fix, (cy_us_t)(1000 + (cy_us_t)i), (uint64_t)(100 + i)));
    }
    TEST_ASSERT_EQUAL_size_t(GOSSIP_DEDUP_CAPACITY, dedup_seen_count(&fix));
    TEST_ASSERT_TRUE(dedup_mark(&fix, 2000, UINT64_C(9999)));
    bool found_oldest = false;
    bool found_new    = false;
    for (size_t i = 0U; i < GOSSIP_DEDUP_CAPACITY; i++) {
        found_oldest = found_oldest || (fix.cy->gossip_dedup[i].hash == UINT64_C(100));
        found_new    = found_new || (fix.cy->gossip_dedup[i].hash == UINT64_C(9999));
    }
    TEST_ASSERT_FALSE(found_oldest);
    TEST_ASSERT_TRUE(found_new);
    fixture_deinit(&fix);
}

static void test_gossip_dedup_update_on_send_prevents_immediate_reforward(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const uint64_t h = gossip_dedup_hash(UINT64_C(0x9999), 4U, 2);
    TEST_ASSERT_TRUE(dedup_mark(&fix, 10, h));
    TEST_ASSERT_FALSE(dedup_mark(&fix, 11, h));
    fixture_deinit(&fix);
}

static void test_gossip_random_peer_except_filters_stale_blacklisted_and_empty(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t now = 10 * MEGA;
    fixture_set_peer(&fix, 0U, UINT64_C(10), now - (GOSSIP_PERIOD_DEFAULT * 4));
    fixture_set_peer(&fix, 1U, UINT64_C(20), now);
    fixture_set_peer(&fix, 2U, UINT64_C(30), now);
    const uint64_t seq[] = { 0U, 1U, 2U, 3U, 4U, 5U };
    fixture_set_random_sequence(&fix, seq, sizeof(seq) / sizeof(seq[0]));

    const uint64_t       blacklist1[] = { UINT64_C(20) };
    gossip_peer_t* const p1           = gossip_random_peer_except(fix.cy, now, 1U, blacklist1);
    TEST_ASSERT_NOT_NULL(p1);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(30), p1->id);

    const uint64_t blacklist2[] = { UINT64_C(20), UINT64_C(30) };
    TEST_ASSERT_NULL(gossip_random_peer_except(fix.cy, now, 2U, blacklist2));
    fixture_deinit(&fix);
}

static void test_gossip_random_peer_except_deterministic_selection_sanity(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t now = 5 * MEGA;
    fixture_set_peer(&fix, 0U, UINT64_C(100), now);
    fixture_set_peer(&fix, 1U, UINT64_C(200), now);
    fixture_set_peer(&fix, 2U, UINT64_C(300), now);
    const uint64_t seq[] = { 0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U };
    fixture_set_random_sequence(&fix, seq, sizeof(seq) / sizeof(seq[0]));

    bool hit100 = false;
    bool hit200 = false;
    bool hit300 = false;
    for (size_t i = 0U; i < 9U; i++) {
        gossip_peer_t* const p = gossip_random_peer_except(fix.cy, now, 0U, NULL);
        TEST_ASSERT_NOT_NULL(p);
        hit100 = hit100 || (p->id == UINT64_C(100));
        hit200 = hit200 || (p->id == UINT64_C(200));
        hit300 = hit300 || (p->id == UINT64_C(300));
    }
    TEST_ASSERT_TRUE(hit100 && hit200 && hit300);
    fixture_deinit(&fix);
}

static void test_send_gossip_raw_no_transport_is_noop(void)
{
    fixture_t fix;
    fixture_init(&fix);
    gossip_begin(fix.cy);
    const cy_err_t err = send_gossip_raw(fix.cy, 100U, 3U, UINT64_C(0xD100000000000001), 0U, 0, str_empty, NULL, NULL);
    TEST_ASSERT_EQUAL_INT(CY_OK, err);
    TEST_ASSERT_EQUAL_size_t(0U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, fix.p2p_send_count);
    fixture_deinit(&fix);
}

static void test_send_gossip_raw_writer_and_lane_paths(void)
{
    fixture_t fix;
    fixture_init(&fix);
    gossip_begin(fix.cy);

    const cy_lane_t lane = make_lane(UINT64_C(0x701), 0x71U);
    cy_err_t        err  = send_gossip_raw(
      fix.cy, 200U, 5U, UINT64_C(0xD100000000000002), 3U, 1, cy_str("gossip/send/raw"), fix.cy->broad_writer, &lane);
    TEST_ASSERT_EQUAL_INT(CY_OK, err);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(1U, fix.p2p_send_count);
    TEST_ASSERT_EQUAL_UINT8(0U, fix.capture[0].ttl); // broadcast forces zero TTL
    TEST_ASSERT_EQUAL_UINT8(0U, fix.capture[1].ttl); // shared frame when both writer and lane are provided
    TEST_ASSERT_EQUAL_UINT64(lane.id, fix.capture[1].lane_id);

    fix.fail_subject_send = true;
    err =
      send_gossip_raw(fix.cy, 201U, 4U, UINT64_C(0xD100000000000003), 1U, 0, str_empty, fix.cy->broad_writer, &lane);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, err);
    TEST_ASSERT_EQUAL_size_t(2U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(1U, fix.p2p_send_count); // writer failure short-circuits p2p send
    fixture_deinit(&fix);
}

static void test_on_gossip_peer_fill_update_and_replacement_policy(void)
{
    fixture_t fix;
    fixture_init(&fix);
    for (size_t i = 0U; i < GOSSIP_PEER_COUNT; i++) {
        fixture_set_peer(&fix, i, UINT64_C(1000) + (uint64_t)i, 10U);
    }
    fixture_set_peer(&fix, 0U, UINT64_C(1000), BIG_BANG);

    const cy_lane_t lane_new = make_lane(UINT64_C(5555), 0xA5U);
    fixture_on_gossip(&fix, 10, 1U, UINT64_C(0x123456), 0U, 0, str_empty, NULL, lane_new);
    gossip_peer_t* peer = gossip_peer_find(fix.cy, UINT64_C(5555));
    TEST_ASSERT_NOT_NULL(peer);
    TEST_ASSERT_EQUAL_INT(10, peer->last_seen);
    TEST_ASSERT_EQUAL_UINT8(0xA5U, peer->p2p.state[0]);

    const cy_lane_t lane_update = make_lane(UINT64_C(5555), 0x5AU);
    fixture_on_gossip(&fix, 20, 1U, UINT64_C(0x123457), 0U, 0, str_empty, NULL, lane_update);
    peer = gossip_peer_find(fix.cy, UINT64_C(5555));
    TEST_ASSERT_NOT_NULL(peer);
    TEST_ASSERT_EQUAL_INT(20, peer->last_seen);
    TEST_ASSERT_EQUAL_UINT8(0x5AU, peer->p2p.state[0]);

    fix.cy->gossip_peer_replacement_moratorium_until = 1000;
    const cy_lane_t lane_blocked                     = make_lane(UINT64_C(7777), 0x77U);
    fixture_on_gossip(&fix, 100, 1U, UINT64_C(0xABCDE0), 0U, 0, str_empty, NULL, lane_blocked);
    TEST_ASSERT_NULL(gossip_peer_find(fix.cy, UINT64_C(7777)));

    fix.cy->gossip_peer_replacement_moratorium_until = 0;
    {
        const uint64_t seq_no_replace[] = { 1U }; // chance false (1 % 8 != 0)
        fixture_set_random_sequence(&fix, seq_no_replace, 1U);
        fixture_on_gossip(&fix, 2000, 1U, UINT64_C(0xABCDE1), 0U, 0, str_empty, NULL, lane_blocked);
        TEST_ASSERT_NULL(gossip_peer_find(fix.cy, UINT64_C(7777)));
    }
    {
        const uint64_t seq_replace[] = { 0U, 3U, 0U }; // chance true, choose slot 3, then dither
        fixture_set_random_sequence(&fix, seq_replace, 3U);
        fixture_on_gossip(&fix, 3000, 1U, UINT64_C(0xABCDE2), 0U, 0, str_empty, NULL, lane_blocked);
        TEST_ASSERT_NOT_NULL(gossip_peer_find(fix.cy, UINT64_C(7777)));
    }
    {
        const cy_us_t  moratorium  = fix.cy->gossip_peer_replacement_moratorium_until;
        const uint64_t seq_again[] = { 0U, 0U, 0U };
        fixture_set_random_sequence(&fix, seq_again, 3U);
        fixture_on_gossip(
          &fix, moratorium - 1, 1U, UINT64_C(0xABCDE3), 0U, 0, str_empty, NULL, make_lane(UINT64_C(8888), 0x88U));
        TEST_ASSERT_NULL(gossip_peer_find(fix.cy, UINT64_C(8888)));
    }
    fixture_deinit(&fix);
}

static void test_on_gossip_peer_replacement_moratorium_boundary_inclusive(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t ts_base = GOSSIP_PERIOD_DEFAULT * 10;

    for (size_t i = 0U; i < GOSSIP_PEER_COUNT; i++) {
        fixture_set_peer(&fix, i, UINT64_C(2000) + (uint64_t)i, ts_base);
    }
    fix.cy->gossip_peer_replacement_moratorium_until = ts_base + 1000;

    const uint64_t seq[] = { 0U, 0U, 0U, 0U, 0U }; // chance=true, deterministic slot/dither
    fixture_set_random_sequence(&fix, seq, sizeof(seq) / sizeof(seq[0]));
    fixture_on_gossip(
      &fix, ts_base + 1000, 1U, UINT64_C(0xC001), 0U, 0, str_empty, NULL, make_lane(UINT64_C(7777), 0x77U));
    TEST_ASSERT_NOT_NULL(gossip_peer_find(fix.cy, UINT64_C(7777)));

    fixture_deinit(&fix);
}

static void test_on_gossip_ttl_zero_and_duplicate_are_not_forwarded(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t now = 100U;
    fixture_set_peer(&fix, 0U, UINT64_C(10), now);
    fixture_set_peer(&fix, 1U, UINT64_C(20), now);
    fixture_set_peer(&fix, 2U, UINT64_C(30), now);

    const cy_lane_t lane = make_lane(UINT64_C(99), 0x99U);
    fixture_on_gossip(&fix, now, 0U, UINT64_C(0xA1), 1U, 0, str_empty, NULL, lane);
    TEST_ASSERT_EQUAL_size_t(0U, fix.p2p_send_count);

    const uint64_t seq[] = { 0U, 1U, 2U, 3U, 4U, 5U };
    fixture_set_random_sequence(&fix, seq, sizeof(seq) / sizeof(seq[0]));
    fixture_on_gossip(&fix, now + 1, 5U, UINT64_C(0xA2), 2U, 0, str_empty, NULL, lane);
    const size_t first_count = fix.p2p_send_count;
    TEST_ASSERT_TRUE(first_count > 0U);
    fixture_on_gossip(&fix, now + 2, 5U, UINT64_C(0xA2), 2U, 0, str_empty, NULL, lane);
    TEST_ASSERT_EQUAL_size_t(first_count, fix.p2p_send_count);

    fixture_deinit(&fix);
}

static void test_on_gossip_forward_decrements_ttl_blacklists_sender_and_limits_fanout(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t now = 200U;
    fixture_set_peer(&fix, 0U, UINT64_C(99), now); // sender, must be excluded
    fixture_set_peer(&fix, 1U, UINT64_C(10), now);
    fixture_set_peer(&fix, 2U, UINT64_C(20), now);
    fixture_set_peer(&fix, 3U, UINT64_C(30), now);

    const uint64_t seq[] = { 0U, 1U, 2U, 3U };
    fixture_set_random_sequence(&fix, seq, sizeof(seq) / sizeof(seq[0]));
    fixture_on_gossip(&fix, now, 7U, UINT64_C(0xB1), 3U, 1, str_empty, NULL, make_lane(UINT64_C(99), 0x11U));
    TEST_ASSERT_EQUAL_size_t(GOSSIP_OUTDEGREE, fix.p2p_send_count);
    TEST_ASSERT_FALSE(capture_has_lane(&fix, UINT64_C(99)));
    for (size_t i = 0U; i < fix.capture_count; i++) {
        TEST_ASSERT_EQUAL_UINT8(header_gossip, fix.capture[i].type);
        TEST_ASSERT_EQUAL_UINT8(6U, fix.capture[i].ttl);
    }
    fixture_deinit(&fix);
}

static void test_on_gossip_local_win_suppresses_forward_and_schedules_urgent(void)
{
    fixture_t fix;
    fixture_init(&fix);
    cy_topic_t* const topic = fixture_make_topic(&fix, "gossip/local/win", 5U);
    topic_merge_lage(topic, 1000, 5);
    fixture_set_peer(&fix, 0U, UINT64_C(10), 1000);
    fixture_set_peer(&fix, 1U, UINT64_C(20), 1000);
    const uint64_t evictions_before = topic->evictions;
    fixture_on_gossip(&fix, 1000, 5U, topic->hash, 4U, 1, str_empty, NULL, make_lane(UINT64_C(50), 0x22U));
    TEST_ASSERT_EQUAL_UINT64(evictions_before, topic->evictions);
    TEST_ASSERT_EQUAL_size_t(0U, fix.p2p_send_count);
    TEST_ASSERT_TRUE(is_listed(&fix.cy->list_gossip_urgent, &topic->list_gossip_urgent));
    fixture_deinit(&fix);
}

static void test_on_gossip_local_lose_forwards_merged_state(void)
{
    fixture_t fix;
    fixture_init(&fix);
    cy_topic_t* const topic = fixture_make_topic(&fix, "gossip/local/lose", 1U);
    topic_merge_lage(topic, 2000, 1);
    fixture_set_peer(&fix, 0U, UINT64_C(10), 2000);
    fixture_set_peer(&fix, 1U, UINT64_C(20), 2000);
    const uint64_t seq[] = { 0U, 1U, 2U, 3U };
    fixture_set_random_sequence(&fix, seq, sizeof(seq) / sizeof(seq[0]));
    fixture_on_gossip(&fix, 2000, 4U, topic->hash, 9U, 1, str_empty, NULL, make_lane(UINT64_C(40), 0x33U));
    TEST_ASSERT_EQUAL_UINT32(9U, topic->evictions);
    TEST_ASSERT_TRUE(fix.p2p_send_count > 0U);
    TEST_ASSERT_EQUAL_UINT8(header_gossip, fix.capture[0].type);
    TEST_ASSERT_EQUAL_UINT8(3U, fix.capture[0].ttl);
    TEST_ASSERT_EQUAL_UINT64(topic->hash, fix.capture[0].hash);
    TEST_ASSERT_EQUAL_UINT32(topic->evictions, fix.capture[0].evictions);
    fixture_deinit(&fix);
}

static void test_on_gossip_unknown_out_topic_forward_and_error_reporting(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t now = 4000U;

    fixture_set_peer(&fix, 0U, UINT64_C(10), now);
    fixture_set_peer(&fix, 1U, UINT64_C(20), now);
    fixture_set_peer(&fix, 2U, UINT64_C(30), now);
    const uint64_t seq[] = { 0U, 1U, 2U, 3U };
    fixture_set_random_sequence(&fix, seq, sizeof(seq) / sizeof(seq[0]));

    cy_topic_t  dummy_topic = { 0 };
    cy_topic_t* out_topic   = &dummy_topic;
    fix.fail_p2p_send       = true;
    fixture_on_gossip(
      &fix, now, 3U, UINT64_C(0x1000000000AA0011), 2U, 0, str_empty, &out_topic, make_lane(UINT64_C(999), 0x99U));
    TEST_ASSERT_NULL(out_topic);
    TEST_ASSERT_TRUE(fix.p2p_send_count > 0U);    // unknown topic gossip forwarded
    TEST_ASSERT_TRUE(fix.async_error_count > 0U); // forwarding failures reported
    fixture_deinit(&fix);
}

static void test_on_scout_broadcast_soon_and_unicast_paths(void)
{
    fixture_t fix;
    fixture_init(&fix);
    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "gossip/scout/cb/topic", 0U);
    const cy_lane_t   lane  = make_lane(UINT64_C(0xCAFE), 0xCAU);
    const cy_us_t     now   = 1000U;

    fix.cy->gossip_next = now + (KILO * 50); // <= now+100k, broadcast soon
    on_scout(fix.cy, now, cy_str("gossip/scout/cb/>"), lane);
    TEST_ASSERT_EQUAL_size_t(0U, fix.p2p_send_count);

    fix.cy->gossip_next = now + (KILO * 200); // > now+100k, unicast scout response
    on_scout(fix.cy, now + 1U, cy_str("gossip/scout/cb/>"), lane);
    TEST_ASSERT_TRUE(fix.p2p_send_count > 0U);
    TEST_ASSERT_EQUAL_UINT8(header_gossip, fix.capture[fix.capture_count - 1U].type);
    TEST_ASSERT_EQUAL_UINT64(topic->hash, fix.capture[fix.capture_count - 1U].hash);
    fixture_deinit(&fix);
}

static void test_gossip_poll_broadcast_path_due_and_dedup_success_only(void)
{
    fixture_t fix;
    fixture_init(&fix);
    fixture_set_now(&fix, 1000);
    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "gossip/poll/broadcast", 0U);
    fix.cy->gossip_next     = 1000;

    fix.fail_subject_send = true;
    gossip_poll(fix.cy, 1000);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, dedup_seen_count(&fix));

    fix.fail_subject_send = false;
    fix.cy->gossip_next   = 1001;
    gossip_poll(fix.cy, 1001);
    TEST_ASSERT_TRUE(dedup_seen_count(&fix) > 0U);
    TEST_ASSERT_TRUE(fix.cy->gossip_next > 1001);
    (void)topic;
    fixture_deinit(&fix);
}

static void test_gossip_poll_urgent_path_and_unique_unicast(void)
{
    fixture_t fix;
    fixture_init(&fix);
    fixture_set_now(&fix, 3000);
    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "gossip/poll/urgent", 0U);
    schedule_gossip_urgent(topic);
    fix.cy->gossip_next = 4000;
    fixture_set_peer(&fix, 0U, UINT64_C(10), 3000);
    fixture_set_peer(&fix, 1U, UINT64_C(20), 3000);
    fixture_set_peer(&fix, 2U, UINT64_C(30), 3000);
    const uint64_t seq[] = { 0U, 1U, 2U, 3U };
    fixture_set_random_sequence(&fix, seq, sizeof(seq) / sizeof(seq[0]));
    gossip_poll(fix.cy, 3000);
    TEST_ASSERT_EQUAL_size_t(0U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(GOSSIP_OUTDEGREE, fix.p2p_send_count);
    TEST_ASSERT_NOT_EQUAL(fix.capture[0].lane_id, fix.capture[1].lane_id);
    TEST_ASSERT_FALSE(is_listed(&fix.cy->list_gossip_urgent, &topic->list_gossip_urgent));
    fixture_deinit(&fix);
}

static void test_gossip_poll_urgent_rate_limit_same_topic_requeue(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t t0 = 3000000;
    fixture_set_now(&fix, t0);

    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "gossip/poll/urgent/rate-limit/requeue", 0U);
    topic_merge_lage(topic, t0, 20);        // keep log-age stable over the short test interval
    fix.cy->gossip_next = t0 + (10 * MEGA); // keep urgent path selected
    fixture_set_peer(&fix, 0U, UINT64_C(10), t0);
    fixture_set_peer(&fix, 1U, UINT64_C(20), t0);
    fixture_set_peer(&fix, 2U, UINT64_C(30), t0);

    schedule_gossip_urgent(topic);
    gossip_poll(fix.cy, t0);
    const size_t first = fix.p2p_send_count;
    TEST_ASSERT_EQUAL_size_t(GOSSIP_OUTDEGREE, first);

    schedule_gossip_urgent(topic);
    gossip_poll(fix.cy, t0 + 1);
    TEST_ASSERT_EQUAL_size_t(first, fix.p2p_send_count); // same fault requeued too soon => rate-limited

    schedule_gossip_urgent(topic);
    gossip_poll(fix.cy, t0 + GOSSIP_DEDUP_TIMEOUT);
    TEST_ASSERT_EQUAL_size_t(first, fix.p2p_send_count); // strict boundary: still not fresh

    schedule_gossip_urgent(topic);
    gossip_poll(fix.cy, t0 + GOSSIP_DEDUP_TIMEOUT + 1);
    TEST_ASSERT_EQUAL_size_t(first + GOSSIP_OUTDEGREE, fix.p2p_send_count);
    fixture_deinit(&fix);
}

static void test_gossip_poll_urgent_rate_limit_repeated_fault_detection(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t t0 = 5000000;
    fixture_set_now(&fix, t0);

    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "gossip/poll/urgent/rate-limit/fault", 5U);
    topic_merge_lage(topic, t0, 20);        // keep log-age stable; we want "same fault" hash throughout
    fix.cy->gossip_next = t0 + (10 * MEGA); // keep urgent path selected
    fixture_set_peer(&fix, 0U, UINT64_C(10), t0);
    fixture_set_peer(&fix, 1U, UINT64_C(20), t0);
    fixture_set_peer(&fix, 2U, UINT64_C(30), t0);

    // Same incoming divergence repeatedly: local wins each time, so the same repair gossip is requested repeatedly.
    const cy_lane_t lane = make_lane(UINT64_C(999), 0x99U);
    fixture_on_gossip(&fix, t0, 4U, topic->hash, 4U, 0, str_empty, NULL, lane);
    gossip_poll(fix.cy, t0);
    const size_t first = fix.p2p_send_count;
    TEST_ASSERT_EQUAL_size_t(GOSSIP_OUTDEGREE, first);

    fixture_on_gossip(&fix, t0 + 1, 4U, topic->hash, 4U, 0, str_empty, NULL, lane);
    gossip_poll(fix.cy, t0 + 1);
    TEST_ASSERT_EQUAL_size_t(first, fix.p2p_send_count); // repeated same fault within timeout => no new epidemic send

    fixture_on_gossip(&fix, t0 + GOSSIP_DEDUP_TIMEOUT + 1, 4U, topic->hash, 4U, 0, str_empty, NULL, lane);
    gossip_poll(fix.cy, t0 + GOSSIP_DEDUP_TIMEOUT + 1);
    TEST_ASSERT_EQUAL_size_t(first + GOSSIP_OUTDEGREE, fix.p2p_send_count); // allowed again after timeout
    fixture_deinit(&fix);
}

static void test_gossip_poll_urgent_drop_when_no_eligible_and_dedup_on_success_only(void)
{
    fixture_t fix;
    fixture_init(&fix);
    fixture_set_now(&fix, 5000);
    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "gossip/poll/urgent/drop", 0U);
    fix.cy->gossip_next     = 6000;
    schedule_gossip_urgent(topic);
    gossip_poll(fix.cy, 5000);
    TEST_ASSERT_EQUAL_size_t(0U, fix.p2p_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, dedup_seen_count(&fix));

    fixture_set_peer(&fix, 0U, UINT64_C(10), 5001);
    fixture_set_peer(&fix, 1U, UINT64_C(20), 5001);
    schedule_gossip_urgent(topic);
    fix.fail_p2p_send = true;
    gossip_poll(fix.cy, 5001);
    TEST_ASSERT_EQUAL_size_t(0U, dedup_seen_count(&fix));

    schedule_gossip_urgent(topic);
    fix.fail_p2p_send = false;
    gossip_poll(fix.cy, 5002);
    TEST_ASSERT_TRUE(dedup_seen_count(&fix) > 0U);
    fixture_deinit(&fix);
}

static void test_gossip_poll_urgent_failed_epidemic_does_not_rate_limit_retry(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t t0 = 6000000;
    fixture_set_now(&fix, t0);

    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "gossip/poll/urgent/fail/no-cache", 0U);
    topic_merge_lage(topic, t0, 20);        // keep log-age stable over the short test interval
    fix.cy->gossip_next = t0 + (10 * MEGA); // keep urgent path selected
    fixture_set_peer(&fix, 0U, UINT64_C(10), t0);
    fixture_set_peer(&fix, 1U, UINT64_C(20), t0);
    fixture_set_peer(&fix, 2U, UINT64_C(30), t0);

    schedule_gossip_urgent(topic);
    fix.fail_p2p_send = true;
    gossip_poll(fix.cy, t0);
    TEST_ASSERT_EQUAL_size_t(GOSSIP_OUTDEGREE, fix.p2p_send_count); // attempted but failed
    TEST_ASSERT_EQUAL_size_t(0U, dedup_seen_count(&fix));           // failed epidemic must not update dedup cache

    schedule_gossip_urgent(topic);
    fix.fail_p2p_send = false;
    gossip_poll(fix.cy, t0 + 1);
    TEST_ASSERT_EQUAL_size_t(2U * GOSSIP_OUTDEGREE, fix.p2p_send_count); // immediate retry allowed
    TEST_ASSERT_TRUE(dedup_seen_count(&fix) > 0U);

    schedule_gossip_urgent(topic);
    gossip_poll(fix.cy, t0 + 2);
    TEST_ASSERT_EQUAL_size_t(2U * GOSSIP_OUTDEGREE, fix.p2p_send_count); // now rate-limited by successful send
    fixture_deinit(&fix);
}

static void test_gossip_poll_urgent_suppressed_if_same_gossip_was_broadcast_just_now(void)
{
    fixture_t fix;
    fixture_init(&fix);
    const cy_us_t t0 = 7000000;
    fixture_set_now(&fix, t0);

    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "gossip/poll/urgent/after-broadcast", 0U);
    topic_merge_lage(topic, t0, 20); // keep log-age stable across timeout checks
    fix.cy->gossip_next = t0;        // force broadcast on first poll
    fixture_set_peer(&fix, 0U, UINT64_C(10), t0);
    fixture_set_peer(&fix, 1U, UINT64_C(20), t0);
    fixture_set_peer(&fix, 2U, UINT64_C(30), t0);

    gossip_poll(fix.cy, t0);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, fix.p2p_send_count);

    schedule_gossip_urgent(topic);
    gossip_poll(fix.cy, t0 + 1);
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, fix.p2p_send_count); // immediate epidemic resend would be redundant, so suppressed

    schedule_gossip_urgent(topic);
    gossip_poll(fix.cy, t0 + GOSSIP_DEDUP_TIMEOUT + 1);
    TEST_ASSERT_EQUAL_size_t(GOSSIP_OUTDEGREE, fix.p2p_send_count); // resend allowed once dedup timeout elapsed
    fixture_deinit(&fix);
}

static void test_gossip_poll_urgent_failed_send_does_not_evict_existing_dedup_entries(void)
{
    fixture_t fix;
    fixture_init(&fix);
    fixture_set_now(&fix, 7000);

    for (size_t i = 0U; i < GOSSIP_DEDUP_CAPACITY; i++) {
        TEST_ASSERT_TRUE(dedup_mark(&fix, (cy_us_t)(1000 + i), UINT64_C(0xA000000000000000) + (uint64_t)i));
    }
    const uint64_t oldest_hash = UINT64_C(0xA000000000000000);
    TEST_ASSERT_TRUE(dedup_has_hash(&fix, oldest_hash));

    cy_topic_t* const topic       = fixture_make_explicit_topic(&fix, "gossip/poll/urgent/no-evict", 0U);
    const uint64_t    urgent_hash = gossip_dedup_hash(topic->hash, topic->evictions, topic_lage(topic, 7000));
    TEST_ASSERT_FALSE(dedup_has_hash(&fix, urgent_hash));

    fix.cy->gossip_next = 8000;
    schedule_gossip_urgent(topic);
    gossip_poll(fix.cy, 7000); // no peers => no successful sends => dedup table must remain unchanged.
    TEST_ASSERT_EQUAL_size_t(0U, fix.p2p_send_count);
    TEST_ASSERT_TRUE(dedup_has_hash(&fix, oldest_hash));
    TEST_ASSERT_FALSE(dedup_has_hash(&fix, urgent_hash));
    fixture_deinit(&fix);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_gossip_dedup_first_duplicate_and_expiry);
    RUN_TEST(test_gossip_dedup_expiry_boundary_is_strictly_greater_than_timeout);
    RUN_TEST(test_gossip_dedup_capacity_eviction_replaces_oldest);
    RUN_TEST(test_gossip_dedup_update_on_send_prevents_immediate_reforward);
    RUN_TEST(test_gossip_random_peer_except_filters_stale_blacklisted_and_empty);
    RUN_TEST(test_gossip_random_peer_except_deterministic_selection_sanity);
    RUN_TEST(test_send_gossip_raw_no_transport_is_noop);
    RUN_TEST(test_send_gossip_raw_writer_and_lane_paths);
    RUN_TEST(test_on_gossip_peer_fill_update_and_replacement_policy);
    RUN_TEST(test_on_gossip_peer_replacement_moratorium_boundary_inclusive);
    RUN_TEST(test_on_gossip_ttl_zero_and_duplicate_are_not_forwarded);
    RUN_TEST(test_on_gossip_forward_decrements_ttl_blacklists_sender_and_limits_fanout);
    RUN_TEST(test_on_gossip_local_win_suppresses_forward_and_schedules_urgent);
    RUN_TEST(test_on_gossip_local_lose_forwards_merged_state);
    RUN_TEST(test_on_gossip_unknown_out_topic_forward_and_error_reporting);
    RUN_TEST(test_on_scout_broadcast_soon_and_unicast_paths);
    RUN_TEST(test_gossip_poll_broadcast_path_due_and_dedup_success_only);
    RUN_TEST(test_gossip_poll_urgent_path_and_unique_unicast);
    RUN_TEST(test_gossip_poll_urgent_rate_limit_same_topic_requeue);
    RUN_TEST(test_gossip_poll_urgent_rate_limit_repeated_fault_detection);
    RUN_TEST(test_gossip_poll_urgent_drop_when_no_eligible_and_dedup_on_success_only);
    RUN_TEST(test_gossip_poll_urgent_failed_epidemic_does_not_rate_limit_retry);
    RUN_TEST(test_gossip_poll_urgent_suppressed_if_same_gossip_was_broadcast_just_now);
    RUN_TEST(test_gossip_poll_urgent_failed_send_does_not_evict_existing_dedup_entries);
    return UNITY_END();
}
