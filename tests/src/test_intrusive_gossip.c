#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include "intrusive_fixture_utils.h"
#include <string.h>

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

    subject_tracker_t active_readers;
    subject_tracker_t active_writers;
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
    return intrusive_random_lcg(&self->rand_state);
}

static cy_subject_writer_t* fixture_subject_writer_new(cy_platform_t* const platform, const uint32_t subject_id)
{
    fixture_t* const           self = fixture_from(platform);
    cy_subject_writer_t* const w    = intrusive_subject_writer_new(&self->heap, subject_id);
    if (w != NULL) {
        subject_tracker_add(&self->active_writers, subject_id);
    }
    return w;
}

static void fixture_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    fixture_t* const self = fixture_from(platform);
    subject_tracker_remove(&self->active_writers, writer->subject_id);
    intrusive_subject_writer_destroy(&self->heap, writer);
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
    fixture_t* const           self = fixture_from(platform);
    cy_subject_reader_t* const r    = intrusive_subject_reader_new(&self->heap, subject_id, extent);
    if (r != NULL) {
        subject_tracker_add(&self->active_readers, subject_id);
    }
    return r;
}

static void fixture_subject_reader_extent_set(cy_platform_t* const       platform,
                                              cy_subject_reader_t* const reader,
                                              const size_t               extent)
{
    fixture_t* const self = fixture_from(platform);
    subject_tracker_assert_contains(&self->active_readers, reader->subject_id);
    intrusive_subject_reader_extent_set(reader, extent);
}

static void fixture_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    fixture_t* const self = fixture_from(platform);
    subject_tracker_remove(&self->active_readers, reader->subject_id);
    intrusive_subject_reader_destroy(&self->heap, reader);
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
    self->platform.vtable                  = &self->vtable;
    self->platform.subject_id_modulus      = (uint32_t)CY_SUBJECT_ID_MODULUS_16bit;
    self->vtable.subject_writer_new        = fixture_subject_writer_new;
    self->vtable.subject_writer_destroy    = fixture_subject_writer_destroy;
    self->vtable.subject_writer_send       = fixture_subject_writer_send;
    self->vtable.subject_reader_new        = fixture_subject_reader_new;
    self->vtable.subject_reader_extent_set = fixture_subject_reader_extent_set;
    self->vtable.subject_reader_destroy    = fixture_subject_reader_destroy;
    self->vtable.unicast                   = fixture_unicast_send;
    self->vtable.unicast_extent_set        = fixture_unicast_extent_set;
    self->vtable.spin                      = fixture_spin;
    self->vtable.now                       = fixture_now;
    self->vtable.realloc                   = fixture_realloc;
    self->vtable.random                    = fixture_random;
    self->rand_state                       = UINT64_C(0x123456789ABCDEF0);
    self->cy                               = cy_new(&self->platform);
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
    intrusive_assert_heap_clean(&self->heap);
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
    TEST_ASSERT_TRUE(sid1 < fix.cy->broad_reader->subject_id);
    TEST_ASSERT_TRUE(sid2 > CY_SUBJECT_ID_MAX(fix.cy->platform->subject_id_modulus));
    TEST_ASSERT_TRUE(sid2 < fix.cy->broad_reader->subject_id);

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
    TEST_ASSERT_EQUAL_UINT32(fix.cy->broad_reader->subject_id, fix.capture[0].subject_id);

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
    TEST_ASSERT_EQUAL_UINT32(fix.cy->broad_reader->subject_id, fix.capture[0].subject_id);

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
    TEST_ASSERT_EQUAL_UINT32(fix.cy->broad_reader->subject_id, fix.capture[0].subject_id);

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

static void test_gossip_wire_name_excludes_pin_expression(void)
{
    fixture_t fix;
    fixture_init(&fix);

    // Create a pinned topic. Pin=100 means evictions = UINT32_MAX - 100.
    // The name stored in the topic is "gossip/wire/name" (no pin), hash computed from that name.
    const char*       topic_name = "gossip/wire/name";
    const uint64_t    hash       = rapidhash(topic_name, strlen(topic_name));
    const uint32_t    evictions  = UINT32_MAX - 100U; // pinned to subject-ID 100
    cy_topic_t* const topic      = fixture_make_explicit_topic(&fix, topic_name, hash, evictions);

    TEST_ASSERT_TRUE(is_pinned(topic->evictions));

    // Trigger a gossip send via gossip_event_urgent. Reset captures first.
    fix.capture_count           = 0U;
    fix.subject_send_count      = 0U;
    topic->gossip_counter       = 0;
    topic->gossip_event.user    = topic;
    topic->gossip_event.handler = gossip_event_urgent;
    gossip_event_urgent(&fix.cy->olga, &topic->gossip_event, 30 * MEGA);

    // Verify at least one gossip frame was captured.
    TEST_ASSERT_TRUE(fix.capture_count > 0U);

    // Examine each captured gossip frame: the name in the payload must NOT contain '#' or pin digits.
    for (size_t i = 0U; i < fix.capture_count; i++) {
        const send_capture_t* const cap = &fix.capture[i];
        TEST_ASSERT_EQUAL_UINT8(header_gossip, cap->type);
        TEST_ASSERT_TRUE(cap->size >= HEADER_BYTES);

        // Extract the name length from the header (byte 23 = HEADER_BYTES - 1).
        const uint8_t name_len = cap->data[HEADER_BYTES - 1U];
        TEST_ASSERT_TRUE(name_len > 0U);
        TEST_ASSERT_TRUE(HEADER_BYTES + name_len <= cap->size);

        // The name bytes start right after the header.
        const unsigned char* const name_bytes = &cap->data[HEADER_BYTES];

        // Verify no '#' character is present in the wire name.
        for (uint8_t j = 0U; j < name_len; j++) {
            TEST_ASSERT_NOT_EQUAL_CHAR('#', (char)name_bytes[j]);
        }

        // Verify the wire name matches the expected normalized name exactly.
        TEST_ASSERT_EQUAL_UINT8(strlen(topic_name), name_len);
        TEST_ASSERT_EQUAL_MEMORY(topic_name, name_bytes, name_len);
    }

    fixture_deinit(&fix);
}

static void test_gossip_pinned_topic_sends_measured_lage(void)
{
    fixture_t fix;
    fixture_init(&fix);

    // Create a pinned explicit topic. Pin=100 means evictions = UINT32_MAX - 100.
    const char*       topic_name = "gossip/pinned/lage";
    const uint64_t    hash       = rapidhash(topic_name, strlen(topic_name));
    const uint32_t    evictions  = UINT32_MAX - 100U;
    cy_topic_t* const topic      = fixture_make_explicit_topic(&fix, topic_name, hash, evictions);
    TEST_ASSERT_TRUE(is_pinned(topic->evictions));

    // Trigger gossip via send_gossip_multicast and capture the frame.
    fix.capture_count      = 0U;
    fix.subject_send_count = 0U;
    const cy_us_t  now     = 31 * MEGA;
    const cy_err_t err     = send_gossip_multicast(topic, now, fix.cy->broad_writer);
    TEST_ASSERT_EQUAL_INT(CY_OK, err);
    TEST_ASSERT_TRUE(fix.capture_count > 0U);

    const send_capture_t* const cap = &fix.capture[0];
    // Verify header type is header_gossip (8).
    TEST_ASSERT_EQUAL_UINT8(header_gossip, cap->type);
    // Pinned topics emit the ordinary measured log-age like any other topic.
    TEST_ASSERT_EQUAL_INT8(topic_lage(topic, now), cap->lage);
    TEST_ASSERT_EQUAL_UINT8(0x04U, cap->data[3]); // floor(log2(31 s)) = 4
    // Verify the evictions field (offset 16, 4 bytes LE) matches topic->evictions.
    TEST_ASSERT_EQUAL_UINT32(topic->evictions, cap->evictions);
    TEST_ASSERT_EQUAL_UINT32(topic->evictions, deserialize_u32(&cap->data[16]));
    // Verify the hash field (offset 8, 8 bytes LE) matches topic->hash.
    TEST_ASSERT_EQUAL_UINT64(topic->hash, cap->hash);
    TEST_ASSERT_EQUAL_UINT64(topic->hash, deserialize_u64(&cap->data[8]));

    fixture_deinit(&fix);
}

static void test_on_gossip_known_topic_pinned_can_lose_divergence_to_older_state(void)
{
    fixture_t fix;
    fixture_init(&fix);

    // Create a pinned explicit topic. Pin=100 means evictions = UINT32_MAX - 100.
    const char*       topic_name = "gossip/pinned/wins";
    const uint64_t    hash       = rapidhash(topic_name, strlen(topic_name));
    const uint32_t    evictions  = UINT32_MAX - 100U;
    cy_topic_t* const topic      = fixture_make_explicit_topic(&fix, topic_name, hash, evictions);
    TEST_ASSERT_TRUE(is_pinned(topic->evictions));

    const cy_us_t now = 32 * MEGA;
    topic->ts_origin  = now - (1 * MEGA); // lage=0
    unschedule_gossip(topic);

    // Remote has an older non-pinned state. Pinning alone must not make the younger local state win.
    on_gossip_known_topic(fix.cy, now, topic, 5U, 10, gossip_broadcast);

    TEST_ASSERT_EQUAL_UINT32(5U, topic->evictions);
    TEST_ASSERT_FALSE(is_pinned(topic->evictions));

    fixture_deinit(&fix);
}

static void test_on_gossip_known_topic_remote_pinned_low_wire_age_does_not_win(void)
{
    fixture_t fix;
    fixture_init(&fix);
    fix.now = lage_to_us(10) + (20 * MEGA);

    const char*       topic_name = "gossip/pinned/no-normalize/known";
    const uint64_t    hash       = rapidhash(topic_name, strlen(topic_name));
    cy_topic_t* const topic      = fixture_make_explicit_topic(&fix, topic_name, hash, 0U);
    TEST_ASSERT_FALSE(is_pinned(topic->evictions));

    topic->ts_origin = fix.now - lage_to_us(10);
    unschedule_gossip(topic);

    const uint32_t remote_evictions = UINT32_MAX - 25U;
    on_gossip_known_topic(fix.cy, fix.now, topic, remote_evictions, 0, gossip_broadcast);

    TEST_ASSERT_EQUAL_UINT32(0U, topic->evictions);
    TEST_ASSERT_FALSE(is_pinned(topic->evictions));
    TEST_ASSERT_TRUE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));
    TEST_ASSERT_TRUE(topic->gossip_event.handler == gossip_event_urgent);

    fixture_deinit(&fix);
}

static void test_on_gossip_known_topic_equal_lage_higher_evictions_win(void)
{
    fixture_t fix;
    fixture_init(&fix);

    // Create a pinned explicit topic. Pin=100 means evictions = UINT32_MAX - 100.
    const char*       topic_name = "gossip/pinned/minpin";
    const uint64_t    hash       = rapidhash(topic_name, strlen(topic_name));
    const uint32_t    evictions  = UINT32_MAX - 100U;
    cy_topic_t* const topic      = fixture_make_explicit_topic(&fix, topic_name, hash, evictions);
    TEST_ASSERT_TRUE(is_pinned(topic->evictions));

    const cy_us_t now = 33 * MEGA;
    topic->ts_origin  = now - (1 * MEGA); // lage=0
    unschedule_gossip(topic);

    // Remote is also pinned: pin=50 means evictions = UINT32_MAX - 50.
    // Equal log-age falls through to the ordinary higher-evictions tiebreak.
    const uint32_t remote_evictions = UINT32_MAX - 50U;
    on_gossip_known_topic(fix.cy, now, topic, remote_evictions, 0, gossip_broadcast);

    // Remote wins: local adopts remote evictions.
    TEST_ASSERT_EQUAL_UINT32(UINT32_MAX - 50U, topic->evictions);
    // Verify subject-ID matches the new pin value.
    TEST_ASSERT_EQUAL_UINT32(50U, topic_subject_id(topic));

    fixture_deinit(&fix);
}

static void test_on_gossip_unknown_topic_pinned_not_in_index_no_collision(void)
{
    fixture_t fix;
    fixture_init(&fix);

    // Create a pinned explicit topic with pin=100 (subject-ID 100). Not in the subject-ID index.
    const char*       topic_name = "gossip/pinned/nocollision";
    const uint64_t    hash       = rapidhash(topic_name, strlen(topic_name));
    const uint32_t    evictions  = UINT32_MAX - 100U;
    cy_topic_t* const topic      = fixture_make_explicit_topic(&fix, topic_name, hash, evictions);
    TEST_ASSERT_TRUE(is_pinned(topic->evictions));
    TEST_ASSERT_EQUAL_UINT32(100U, topic_subject_id(topic));

    // Verify the pinned topic is indeed NOT in the subject-ID index.
    TEST_ASSERT_NULL(topic_find_by_subject_id(fix.cy, 100U));

    const cy_us_t now = 34 * MEGA;
    unschedule_gossip(topic);

    // Construct a remote non-pinned topic whose subject-ID also maps to 100 -- impossible by design,
    // since non-pinned subject-IDs are always > CY_SUBJECT_ID_PINNED_MAX. Instead, use a remote pinned
    // topic with the same subject-ID (pin=100) but a different hash. on_gossip_unknown_topic computes
    // subject_id_impl(remote_hash, remote_evictions) and then looks up topic_find_by_subject_id.
    // Since the pinned topic is not in the index, the lookup returns NULL and nothing happens.
    const uint64_t remote_hash      = hash + 1U;         // different topic
    const uint32_t remote_evictions = UINT32_MAX - 100U; // same pin => same subject-ID 100
    on_gossip_unknown_topic(fix.cy, now, remote_hash, remote_evictions, 0);

    // Pinned topic is unaffected.
    TEST_ASSERT_EQUAL_UINT32(UINT32_MAX - 100U, topic->evictions);
    // No urgent gossip was scheduled from this call (gossip was unscheduled before the call).
    TEST_ASSERT_FALSE(olga_is_pending(&fix.cy->olga, &topic->gossip_event));

    fixture_deinit(&fix);
}

static void test_topic_subscribe_if_matching_pinned_low_wire_age_preserves_age(void)
{
    fixture_t fix;
    fixture_init(&fix);
    fix.now = 21 * MEGA;

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("gossip/pinned/auto/*"), 64U);
    TEST_ASSERT_NOT_NULL(sub);

    const cy_str_t name      = cy_str("gossip/pinned/auto/topic");
    const uint64_t hash      = rapidhash(name.str, name.len);
    const uint32_t evictions = UINT32_MAX - 25U;
    cy_topic_t*    topic     = topic_subscribe_if_matching(fix.cy, name, hash, evictions, 0);
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_TRUE(is_pinned(topic->evictions));
    TEST_ASSERT_EQUAL_UINT32(evictions, topic->evictions);
    TEST_ASSERT_EQUAL_INT(0, topic_lage(topic, fix.now));
    TEST_ASSERT_EQUAL_INT64((int64_t)(fix.now - lage_to_us(0)), (int64_t)topic->ts_origin);
    TEST_ASSERT_NULL(topic_find_by_subject_id(fix.cy, topic_subject_id(topic)));

    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(fix.cy));
    fixture_deinit(&fix);
}

// Validate subscriber pattern index lifecycle through the gossip/subscriber infrastructure.
// When a pattern subscriber is created (even if scouting fails), the pattern index must be
// populated, and when the subscriber is destroyed, the pattern index must be cleaned up.
// This exercises the ensure_subscriber_root pattern index paths (lines 3630-3635).
static void test_subscriber_pattern_index_lifecycle_with_scout_failure(void)
{
    fixture_t fix;
    fixture_init(&fix);

    // Force scouting to fail so that needs_scouting is set on the root.
    fix.fail_subject_send = true;
    fix.async_error_count = 0U;

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("gossip/sub/pattern/lifecycle/*"), 64U);
    // Subscribe succeeds even if scouting fails (scout failure is non-fatal, async error reported).
    TEST_ASSERT_NOT_NULL(sub);
    TEST_ASSERT_TRUE(fix.async_error_count > 0U);

    // Verify the pattern is in the subscriber indexes.
    TEST_ASSERT_FALSE(wkv_is_empty(&fix.cy->subscribers_by_pattern));
    TEST_ASSERT_FALSE(wkv_is_empty(&fix.cy->subscribers_by_name));

    // The root should have needs_scouting set because the scout failed.
    const wkv_node_t* const node = wkv_get(&fix.cy->subscribers_by_name, cy_str("gossip/sub/pattern/lifecycle/*"));
    TEST_ASSERT_NOT_NULL(node);
    subscriber_root_t* const root = (subscriber_root_t*)node->value;
    TEST_ASSERT_NOT_NULL(root);
    TEST_ASSERT_TRUE(root->needs_scouting);
    TEST_ASSERT_NOT_NULL(root->index_pattern);

    // Clean up.
    cy_future_destroy(sub);
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(fix.cy));

    // After destroy, the pattern index should be empty.
    TEST_ASSERT_TRUE(wkv_is_empty(&fix.cy->subscribers_by_pattern));
    TEST_ASSERT_TRUE(wkv_is_empty(&fix.cy->subscribers_by_name));

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
    RUN_TEST(test_gossip_wire_name_excludes_pin_expression);
    RUN_TEST(test_gossip_pinned_topic_sends_measured_lage);
    RUN_TEST(test_on_gossip_known_topic_pinned_can_lose_divergence_to_older_state);
    RUN_TEST(test_on_gossip_known_topic_remote_pinned_low_wire_age_does_not_win);
    RUN_TEST(test_on_gossip_known_topic_equal_lage_higher_evictions_win);
    RUN_TEST(test_on_gossip_unknown_topic_pinned_not_in_index_no_collision);
    RUN_TEST(test_topic_subscribe_if_matching_pinned_low_wire_age_preserves_age);
    RUN_TEST(test_subscriber_pattern_index_lifecycle_with_scout_failure);
    return UNITY_END();
}
