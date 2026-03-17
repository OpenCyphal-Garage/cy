#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
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
    bool          unicast;
    uint32_t      subject_id;
    uint64_t      lane_id;
    size_t        size;
    unsigned char data[HEADER_BYTES + CY_TOPIC_NAME_MAX];
    uint8_t       type;
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
    bool fail_unicast_send;

    size_t   subject_send_count;
    size_t   unicast_send_count;
    size_t   async_error_count;
    cy_err_t last_async_error;

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
                         const bool       unicast,
                         const uint32_t   subject_id,
                         const uint64_t   lane_id,
                         const cy_bytes_t message)
{
    if (self->capture_count >= CAPTURE_CAPACITY) {
        return;
    }
    send_capture_t* const out = &self->capture[self->capture_count++];
    memset(out, 0, sizeof(*out));
    out->unicast    = unicast;
    out->subject_id = subject_id;
    out->lane_id    = lane_id;
    out->size       = flatten_fragments(message, out->data, sizeof(out->data));
    if (out->size > 0U) {
        out->type = out->data[0] & 63U;
    }
    if ((out->type == header_gossip) && (out->size >= HEADER_BYTES)) {
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
    guarded_heap_free(&self->heap, reader);
}

static cy_err_t fixture_unicast_send(cy_platform_t* const   platform,
                                     const cy_lane_t* const lane,
                                     const cy_us_t          deadline,
                                     const cy_bytes_t       message)
{
    (void)deadline;
    fixture_t* const self = fixture_from(platform);
    self->unicast_send_count++;
    capture_send(self, true, 0U, (lane != NULL) ? lane->id : 0U, message);
    return self->fail_unicast_send ? CY_ERR_MEDIA : CY_OK;
}

static void fixture_unicast_extent_set(cy_platform_t* const platform, const size_t extent)
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
    (void)line;
    fixture_t* const self = fixture_from(cy->platform);
    self->async_error_count++;
    self->last_async_error = error;
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
    self->vtable.unicast                = fixture_unicast_send;
    self->vtable.unicast_extent_set     = fixture_unicast_extent_set;
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

static cy_topic_t* fixture_make_topic(fixture_t* const  self,
                                      const char* const name,
                                      const uint64_t    hash,
                                      const uint32_t    evictions)
{
    cy_topic_t*    out = NULL;
    const cy_err_t er  = topic_new(self->cy, &out, cy_str(name), hash, evictions, LAGE_MIN);
    TEST_ASSERT_EQUAL_INT(CY_OK, er);
    TEST_ASSERT_NOT_NULL(out);
    return out;
}

static cy_topic_t* fixture_make_explicit_topic(fixture_t* const  self,
                                               const char* const name,
                                               const uint64_t    hash,
                                               const uint32_t    evictions)
{
    cy_topic_t* const out = fixture_make_topic(self, name, hash, evictions);
    out->pub_count        = 1U;
    topic_sync_implicit(out);
    TEST_ASSERT_FALSE(is_implicit(out));
    return out;
}

static cy_lane_t make_lane(const uint64_t id)
{
    cy_lane_t out    = { .id = id, .ctx = { { 0 } }, .prio = cy_prio_nominal };
    out.ctx.state[0] = (byte_t)(id & 0xFFU);
    return out;
}

static bool all_captures_match_lane(const fixture_t* const fix, const uint64_t lane_id)
{
    for (size_t i = 0U; i < fix->capture_count; i++) {
        if (!fix->capture[i].unicast || (fix->capture[i].lane_id != lane_id)) {
            return false;
        }
    }
    return true;
}

static void test_topic_gossip_shard_subject_id_deterministic_and_bounded(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const uint64_t h1   = UINT64_C(0x1000000000001201);
    const uint64_t h2   = UINT64_C(0x1000000000001302);
    const uint32_t sid1 = topic_gossip_shard_subject_id(fix.cy, h1);
    const uint32_t sid2 = topic_gossip_shard_subject_id(fix.cy, h2);

    TEST_ASSERT_EQUAL_UINT32(sid1, topic_gossip_shard_subject_id(fix.cy, h1));
    TEST_ASSERT_TRUE(sid1 > CY_SUBJECT_ID_MAX(fix.cy->platform->subject_id_modulus));
    TEST_ASSERT_TRUE(sid1 < cy_broadcast_subject_id(fix.cy->platform));
    TEST_ASSERT_TRUE(sid2 > CY_SUBJECT_ID_MAX(fix.cy->platform->subject_id_modulus));
    TEST_ASSERT_TRUE(sid2 < cy_broadcast_subject_id(fix.cy->platform));

    fixture_deinit(&fix);
}

static void test_send_gossip_raw_writer_lane_and_noop_paths(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_lane_t lane = make_lane(UINT64_C(0x99));
    const cy_str_t  name = cy_str("intrusive/gossip/raw");

    TEST_ASSERT_EQUAL_INT(CY_OK, send_gossip_raw(fix.cy, 1000, UINT64_C(0x1000000000001234), 7U, -2, name, NULL, NULL));
    TEST_ASSERT_EQUAL_size_t(0U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, fix.unicast_send_count);

    TEST_ASSERT_EQUAL_INT(
      CY_OK, send_gossip_raw(fix.cy, 1000, UINT64_C(0x1000000000001234), 7U, -2, name, fix.cy->broad_writer, NULL));
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, fix.unicast_send_count);

    TEST_ASSERT_EQUAL_INT(CY_OK,
                          send_gossip_raw(fix.cy, 1000, UINT64_C(0x1000000000001234), 7U, -2, name, NULL, &lane));
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(1U, fix.unicast_send_count);

    TEST_ASSERT_EQUAL_INT(
      CY_OK, send_gossip_raw(fix.cy, 1000, UINT64_C(0x1000000000001234), 7U, -2, name, fix.cy->broad_writer, &lane));
    TEST_ASSERT_EQUAL_size_t(2U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(2U, fix.unicast_send_count);
    TEST_ASSERT_TRUE(fix.capture_count >= 2U);
    TEST_ASSERT_EQUAL_UINT8(header_gossip, fix.capture[fix.capture_count - 1U].type);
    TEST_ASSERT_EQUAL_INT8(-2, fix.capture[fix.capture_count - 1U].lage);

    fixture_deinit(&fix);
}

static void test_send_gossip_raw_writer_failure_skips_unicast(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_lane_t lane = make_lane(UINT64_C(0x101));
    const cy_str_t  name = cy_str("intrusive/gossip/raw/fail");

    fix.fail_subject_send = true;
    TEST_ASSERT_EQUAL_INT(
      CY_ERR_MEDIA,
      send_gossip_raw(fix.cy, 1000, UINT64_C(0x1000000000001235), 0U, -1, name, fix.cy->broad_writer, &lane));
    TEST_ASSERT_EQUAL_size_t(1U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, fix.unicast_send_count);

    fixture_deinit(&fix);
}

static void test_schedule_gossip_periodic_requires_nonimplicit_nonpinned_topic(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_topic_t* const explicit_topic =
      fixture_make_explicit_topic(&fix, "intrusive/gossip/explicit#1000000000001200", UINT64_C(0x1000000000001200), 0U);
    cy_topic_t* const pinned_topic = fixture_make_topic(&fix, "intrusive/gossip/pinned", UINT64_C(123), 0U);

    unschedule_gossip(explicit_topic);
    schedule_gossip_periodic(explicit_topic, 1000, false);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &explicit_topic->gossip_event));
    TEST_ASSERT_TRUE(explicit_topic->gossip_event.handler == gossip_event_periodic);

    schedule_gossip_periodic(pinned_topic, 1000, false);
    TEST_ASSERT_FALSE(olga_is_pending(&fix.cy->olga, &pinned_topic->gossip_event));

    fixture_deinit(&fix);
}

static void test_schedule_gossip_urgent_preempts_periodic_deadline(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_topic_t* const topic =
      fixture_make_explicit_topic(&fix, "intrusive/gossip/urgent#1000000000001201", UINT64_C(0x1000000000001201), 0U);

    unschedule_gossip(topic);

    const uint64_t seq_periodic[] = { UINT64_C(0xFFFFFFFFFFFFFFFF) };
    fixture_set_random_sequence(&fix, seq_periodic, 1U);
    schedule_gossip_periodic(topic, 10 * MEGA, false);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
    const cy_us_t periodic_deadline = topic->gossip_event.deadline;

    const uint64_t seq_urgent[] = { 0U };
    fixture_set_random_sequence(&fix, seq_urgent, 1U);
    schedule_gossip_urgent(topic, 10 * MEGA);

    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
    TEST_ASSERT_TRUE(topic->gossip_event.handler == gossip_event_urgent);
    TEST_ASSERT_TRUE(topic->gossip_event.deadline <= periodic_deadline);

    fixture_deinit(&fix);
}

static void test_on_gossip_known_topic_local_win_schedules_urgent(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_us_t     now   = 20 * MEGA;
    cy_topic_t* const topic = fixture_make_explicit_topic(
      &fix, "intrusive/gossip/known/win#1000000000001202", UINT64_C(0x1000000000001202), 6U);

    topic_merge_lage(topic, now, 5);
    unschedule_gossip(topic);

    on_gossip_known_topic(fix.cy, now, topic, 5U, topic_lage(topic, now), gossip_unicast);

    TEST_ASSERT_EQUAL_UINT32(6U, topic->evictions);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
    TEST_ASSERT_TRUE(topic->gossip_event.handler == gossip_event_urgent);

    fixture_deinit(&fix);
}

static void test_on_gossip_known_topic_local_loss_reallocates_and_suppresses_urgent_when_not_needed(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_us_t     now   = 21 * MEGA;
    cy_topic_t* const topic = fixture_make_explicit_topic(
      &fix, "intrusive/gossip/known/loss#1000000000001203", UINT64_C(0x1000000000001203), 1U);

    topic_merge_lage(topic, now, 1);
    unschedule_gossip(topic);

    on_gossip_known_topic(fix.cy, now, topic, 4U, 8, gossip_broadcast);

    TEST_ASSERT_EQUAL_UINT32(4U, topic->evictions);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
    TEST_ASSERT_TRUE(topic->gossip_event.handler == gossip_event_periodic);

    fixture_deinit(&fix);
}

static void test_on_gossip_known_topic_consensus_scope_suppression_rules(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_us_t     now   = 22 * MEGA;
    cy_topic_t* const topic = fixture_make_explicit_topic(
      &fix, "intrusive/gossip/known/consensus#1000000000001204", UINT64_C(0x1000000000001204), 0U);

    topic_merge_lage(topic, now, 3);
    unschedule_gossip(topic);

    const uint64_t seq_unsuppressed[] = { 0U };
    fixture_set_random_sequence(&fix, seq_unsuppressed, 1U);
    schedule_gossip_periodic(topic, now, false);
    const cy_us_t baseline_deadline = topic->gossip_event.deadline;

    const uint64_t seq_broadcast[] = { 0U };
    fixture_set_random_sequence(&fix, seq_broadcast, 1U);
    on_gossip_known_topic(fix.cy, now + 1, topic, topic->evictions, topic_lage(topic, now + 1), gossip_broadcast);
    const cy_us_t suppressed_deadline = topic->gossip_event.deadline;

    TEST_ASSERT_TRUE(topic->gossip_event.handler == gossip_event_periodic);
    TEST_ASSERT_TRUE(suppressed_deadline > baseline_deadline);

    unschedule_gossip(topic);
    fixture_set_random_sequence(&fix, seq_unsuppressed, 1U);
    schedule_gossip_periodic(topic, now, false);
    const cy_us_t unicast_before = topic->gossip_event.deadline;

    on_gossip_known_topic(fix.cy, now + 1, topic, topic->evictions, topic_lage(topic, now + 1), gossip_unicast);
    TEST_ASSERT_EQUAL_UINT64(unicast_before, topic->gossip_event.deadline);

    const uint64_t seq_urgent[] = { 0U };
    fixture_set_random_sequence(&fix, seq_urgent, 1U);
    schedule_gossip_urgent(topic, now);
    TEST_ASSERT_TRUE(topic->gossip_event.handler == gossip_event_urgent);
    const cy_us_t sharded_before = topic->gossip_event.deadline;

    on_gossip_known_topic(fix.cy, now, topic, topic->evictions, topic_lage(topic, now), gossip_sharded);
    TEST_ASSERT_TRUE(topic->gossip_event.handler == gossip_event_urgent);
    TEST_ASSERT_EQUAL_UINT64(sharded_before, topic->gossip_event.deadline);

    fixture_deinit(&fix);
}

static void test_on_gossip_unknown_topic_collision_win_and_loss(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_us_t  now       = 23 * MEGA;
    const uint64_t mod       = (uint64_t)fix.cy->platform->subject_id_modulus;
    const uint64_t base_hash = UINT64_C(0x1000000000001205);
    const uint64_t remote    = base_hash + mod;

    cy_topic_t* const topic = fixture_make_explicit_topic(&fix, "intrusive/gossip/unknown/local", base_hash, 0U);
    topic_merge_lage(topic, now, 4);
    unschedule_gossip(topic);

    on_gossip_unknown_topic(fix.cy, now, remote, 0U, 1);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
    TEST_ASSERT_TRUE(topic->gossip_event.handler == gossip_event_urgent);
    const uint32_t ev_before_loss = topic->evictions;

    on_gossip_unknown_topic(fix.cy, now + MEGA, remote, 0U, 12);
    TEST_ASSERT_TRUE(topic->evictions > ev_before_loss);

    fixture_deinit(&fix);
}

static void test_gossip_event_periodic_uses_broadcast_then_shard_writer(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_topic_t* const topic = fixture_make_explicit_topic(
      &fix, "intrusive/gossip/periodic/shard#1000000000001206", UINT64_C(0x1000000000001206), 0U);

    fix.capture_count      = 0U;
    fix.subject_send_count = 0U;

    topic->gossip_counter       = 0;
    topic->gossip_event.user    = topic;
    topic->gossip_event.handler = gossip_event_periodic;
    gossip_event_periodic(&fix.cy->olga, &topic->gossip_event, 24 * MEGA);

    TEST_ASSERT_TRUE(fix.subject_send_count > 0U);
    TEST_ASSERT_EQUAL_UINT32(cy_broadcast_subject_id(fix.cy->platform), fix.capture[0].subject_id);

    fix.capture_count      = 0U;
    fix.subject_send_count = 0U;
    topic->gossip_counter  = fix.cy->gossip_broadcast_ratio;
    topic->gossip_counter++;
    topic->gossip_event.user    = topic;
    topic->gossip_event.handler = gossip_event_periodic;
    gossip_event_periodic(&fix.cy->olga, &topic->gossip_event, 25 * MEGA);

    TEST_ASSERT_TRUE(fix.subject_send_count > 0U);
    TEST_ASSERT_EQUAL_UINT32(topic_gossip_shard_subject_id(fix.cy, topic->hash), fix.capture[0].subject_id);

    fix.capture_count           = 0U;
    fix.subject_send_count      = 0U;
    topic->gossip_counter       = fix.cy->gossip_broadcast_ratio;
    topic->gossip_event.user    = topic;
    topic->gossip_event.handler = gossip_event_periodic;
    gossip_event_periodic(&fix.cy->olga, &topic->gossip_event, 26 * MEGA);

    TEST_ASSERT_TRUE(fix.subject_send_count > 0U);
    TEST_ASSERT_EQUAL_UINT32(cy_broadcast_subject_id(fix.cy->platform), fix.capture[0].subject_id);

    fixture_deinit(&fix);
}

static void test_gossip_event_periodic_reports_async_error_on_send_failure(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_topic_t* const topic = fixture_make_explicit_topic(
      &fix, "intrusive/gossip/periodic/fail#1000000000001208", UINT64_C(0x1000000000001208), 0U);

    fix.fail_subject_send       = true;
    fix.async_error_count       = 0U;
    fix.subject_send_count      = 0U;
    topic->gossip_counter       = 0;
    topic->gossip_event.user    = topic;
    topic->gossip_event.handler = gossip_event_periodic;
    gossip_event_periodic(&fix.cy->olga, &topic->gossip_event, 27 * MEGA);

    TEST_ASSERT_TRUE(fix.subject_send_count > 0U);
    TEST_ASSERT_EQUAL_size_t(1U, fix.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, fix.last_async_error);

    fixture_deinit(&fix);
}

static void test_gossip_event_urgent_broadcasts_and_resets_counter(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_topic_t* const topic = fixture_make_explicit_topic(
      &fix, "intrusive/gossip/urgent/event#1000000000001207", UINT64_C(0x1000000000001207), 0U);

    fix.capture_count           = 0U;
    fix.subject_send_count      = 0U;
    topic->gossip_counter       = 77;
    topic->gossip_event.user    = topic;
    topic->gossip_event.handler = gossip_event_urgent;

    gossip_event_urgent(&fix.cy->olga, &topic->gossip_event, 26 * MEGA);

    TEST_ASSERT_EQUAL_UINT8(0U, topic->gossip_counter);
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
    TEST_ASSERT_TRUE(topic->gossip_event.handler == gossip_event_periodic);
    TEST_ASSERT_TRUE(fix.subject_send_count > 0U);
    TEST_ASSERT_EQUAL_UINT32(cy_broadcast_subject_id(fix.cy->platform), fix.capture[0].subject_id);

    fixture_deinit(&fix);
}

static void test_on_scout_responds_via_unicast_only(void)
{
    fixture_t fix;
    fixture_init(&fix);

    (void)fixture_make_explicit_topic(
      &fix, "intrusive/gossip/scout/one#1000000000001210", UINT64_C(0x1000000000001210), 0U);
    (void)fixture_make_explicit_topic(
      &fix, "intrusive/gossip/scout/two#1000000000001211", UINT64_C(0x1000000000001211), 0U);

    fix.capture_count      = 0U;
    fix.unicast_send_count = 0U;
    fix.subject_send_count = 0U;

    on_scout(fix.cy, 27 * MEGA, cy_str("intrusive/gossip/scout/>"), make_lane(UINT64_C(0xABC)));

    TEST_ASSERT_EQUAL_size_t(0U, fix.subject_send_count);
    TEST_ASSERT_EQUAL_size_t(2U, fix.unicast_send_count);
    TEST_ASSERT_EQUAL_size_t(2U, fix.capture_count);
    TEST_ASSERT_TRUE(all_captures_match_lane(&fix, UINT64_C(0xABC)));
    TEST_ASSERT_EQUAL_UINT8(header_gossip, fix.capture[0].type);
    TEST_ASSERT_EQUAL_UINT8(header_gossip, fix.capture[1].type);

    fixture_deinit(&fix);
}

static void test_on_scout_reports_async_error_on_unicast_failure(void)
{
    fixture_t fix;
    fixture_init(&fix);

    (void)fixture_make_explicit_topic(
      &fix, "intrusive/gossip/scout/fail/one#1000000000001212", UINT64_C(0x1000000000001212), 0U);
    (void)fixture_make_explicit_topic(
      &fix, "intrusive/gossip/scout/fail/two#1000000000001213", UINT64_C(0x1000000000001213), 0U);

    fix.fail_unicast_send  = true;
    fix.async_error_count  = 0U;
    fix.unicast_send_count = 0U;

    on_scout(fix.cy, 28 * MEGA, cy_str("intrusive/gossip/scout/fail/>"), make_lane(UINT64_C(0xABD)));

    TEST_ASSERT_EQUAL_size_t(2U, fix.unicast_send_count);
    TEST_ASSERT_EQUAL_size_t(2U, fix.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, fix.last_async_error);

    fixture_deinit(&fix);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_topic_gossip_shard_subject_id_deterministic_and_bounded);
    RUN_TEST(test_send_gossip_raw_writer_lane_and_noop_paths);
    RUN_TEST(test_send_gossip_raw_writer_failure_skips_unicast);
    RUN_TEST(test_schedule_gossip_periodic_requires_nonimplicit_nonpinned_topic);
    RUN_TEST(test_schedule_gossip_urgent_preempts_periodic_deadline);
    RUN_TEST(test_on_gossip_known_topic_local_win_schedules_urgent);
    RUN_TEST(test_on_gossip_known_topic_local_loss_reallocates_and_suppresses_urgent_when_not_needed);
    RUN_TEST(test_on_gossip_known_topic_consensus_scope_suppression_rules);
    RUN_TEST(test_on_gossip_unknown_topic_collision_win_and_loss);
    RUN_TEST(test_gossip_event_periodic_uses_broadcast_then_shard_writer);
    RUN_TEST(test_gossip_event_periodic_reports_async_error_on_send_failure);
    RUN_TEST(test_gossip_event_urgent_broadcasts_and_resets_counter);
    RUN_TEST(test_on_scout_responds_via_unicast_only);
    RUN_TEST(test_on_scout_reports_async_error_on_unicast_failure);
    return UNITY_END();
}
