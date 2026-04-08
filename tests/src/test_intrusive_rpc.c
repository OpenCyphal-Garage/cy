#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include "message.h"
#include <stddef.h>
#include <string.h>

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    cy_t                 cy;
    guarded_heap_t       heap;

    size_t fail_after;      ///< Fail N-th new allocation if new_alloc_count >= fail_after.
    size_t new_alloc_count; ///< Counts new allocations only, excludes realloc/free.

    cy_us_t   now;
    uint64_t  random_state;
    cy_err_t  unicast_send_result;
    size_t    unicast_send_count;
    cy_lane_t last_lane;
    cy_us_t   last_deadline;
    byte_t    last_unicast[HEADER_BYTES];
    size_t    last_unicast_size;

    size_t    async_error_count;
    cy_err_t  last_async_error;
    cy_diag_t diag;
} fixture_t;

typedef struct
{
    size_t   count;
    bool     last_done;
    cy_err_t last_error;
} callback_capture_t;

typedef struct
{
    cy_future_t base;
} dummy_publish_future_t;

static size_t g_dummy_publish_dispose_count = 0U; // NOLINT(*-non-const-global-variables)

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    fixture_t* const self = (fixture_t*)platform;
    if ((ptr == NULL) && (size > 0U)) {
        if (self->new_alloc_count >= self->fail_after) {
            return NULL;
        }
        self->new_alloc_count++;
    }
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static cy_us_t fixture_now(cy_platform_t* const platform) { return ((fixture_t*)platform)->now; }

static uint64_t fixture_random(cy_platform_t* const platform)
{
    fixture_t* const self = (fixture_t*)platform;
    self->random_state += UINT64_C(0x9E3779B97F4A7C15);
    return self->random_state;
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

static cy_err_t fixture_unicast_send(cy_platform_t* const   platform,
                                     const cy_lane_t* const lane,
                                     const cy_us_t          deadline,
                                     const cy_bytes_t       message)
{
    fixture_t* const self = (fixture_t*)platform;
    self->unicast_send_count++;
    if (lane != NULL) {
        self->last_lane = *lane;
    } else {
        memset(&self->last_lane, 0, sizeof(self->last_lane));
    }
    self->last_deadline     = deadline;
    self->last_unicast_size = 0U;
    memset(self->last_unicast, 0, sizeof(self->last_unicast));
    for (const cy_bytes_t* seg = &message; seg != NULL; seg = seg->next) {
        if ((seg->size > 0U) && (seg->data != NULL) && (self->last_unicast_size < sizeof(self->last_unicast))) {
            const size_t copy_size = smaller(seg->size, sizeof(self->last_unicast) - self->last_unicast_size);
            memcpy(&self->last_unicast[self->last_unicast_size], seg->data, copy_size);
            self->last_unicast_size += copy_size;
        }
    }
    return self->unicast_send_result;
}

static void fixture_diag_async_error(cy_t* const       cy,
                                     cy_topic_t* const topic,
                                     const cy_err_t    error,
                                     const uint16_t    line_number)
{
    (void)topic;
    (void)line_number;
    fixture_t* const self = (fixture_t*)cy->platform;
    self->async_error_count++;
    self->last_async_error = error;
}

static const cy_diag_vtable_t fixture_diag_vtable = {
    .async_error = fixture_diag_async_error,
};

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0xD9A1F26E3984C57B));
    self->platform.vtable             = &self->vtable;
    self->platform.subject_id_modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_16bit;
    self->platform.cy                 = &self->cy;
    self->vtable.realloc              = fixture_realloc;
    self->vtable.unicast              = fixture_unicast_send;
    self->vtable.unicast_extent_set   = fixture_unicast_extent_set;
    self->vtable.spin                 = fixture_spin;
    self->vtable.now                  = fixture_now;
    self->vtable.random               = fixture_random;
    self->cy.platform                 = &self->platform;
    self->diag                        = (cy_diag_t){ .next = NULL, .vtable = &fixture_diag_vtable };
    cy_diag_add(&self->cy, &self->diag);
    olga_init(&self->cy.olga, &self->cy, olga_now);
    self->cy.ack_baseline_timeout = ACK_BASELINE_DEFAULT_TIMEOUT_us;
    self->fail_after              = SIZE_MAX;
    self->new_alloc_count         = 0U;
    self->now                     = 10000;
    self->random_state            = UINT64_C(0x123456789ABCDEF0);
    self->unicast_send_result     = CY_OK;
    self->last_async_error        = CY_OK;
    self->last_deadline           = BIG_BANG;
    self->last_unicast_size       = 0U;
    self->async_error_count       = 0U;
}

static void fixture_set_fail_after(fixture_t* const self, const size_t fail_after)
{
    self->fail_after      = fail_after;
    self->new_alloc_count = 0U;
}

static void fixture_advance_to(fixture_t* const self, const cy_us_t now)
{
    self->now = now;
    (void)olga_spin(&self->cy.olga);
}

static void fixture_assert_clean(const fixture_t* const self)
{
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self->heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self->heap));
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
}

static void assert_message_counters(const size_t destroyed, const size_t live)
{
    TEST_ASSERT_EQUAL_size_t(destroyed, cy_test_message_destroy_count());
    TEST_ASSERT_EQUAL_size_t(live, cy_test_message_live_count());
}

static cy_message_ts_t make_message(fixture_t* const self, const cy_us_t ts, const byte_t marker)
{
    const byte_t        payload[3] = { marker, (byte_t)(marker + 1U), (byte_t)(marker + 2U) };
    cy_message_t* const msg        = cy_test_message_make(&self->heap, payload, sizeof(payload));
    TEST_ASSERT_NOT_NULL(msg);
    cy_message_ts_t out = { .timestamp = ts, .content = msg };
    return out;
}

static cy_lane_t make_lane(const uint64_t remote_id)
{
    cy_lane_t lane = { 0 };
    lane.id        = remote_id;
    lane.prio      = cy_prio_nominal;
    memcpy(lane.ctx.state, &lane.id, smaller(sizeof(lane.ctx.state), sizeof(lane.id)));
    return lane;
}

static request_future_t* make_request_future(fixture_t* const  fixture,
                                             cy_topic_t* const topic,
                                             const uint64_t    key,
                                             const cy_us_t     liveness_timeout)
{
    memset(topic, 0, sizeof(*topic));
    topic->cy                   = &fixture->cy;
    request_future_t* const out = future_new(&fixture->cy, &request_future_vtable, sizeof(request_future_t));
    TEST_ASSERT_NOT_NULL(out);
    out->topic                           = topic;
    out->liveness_timeout                = liveness_timeout;
    out->last_response.message.timestamp = BIG_BANG;
    out->last_response.message.content   = NULL;
    out->remote_by_id                    = NULL;
    const bool insert_ok                 = future_index_insert(&out->base, &topic->request_futures_by_tag, key);
    TEST_ASSERT_TRUE(insert_ok);
    future_deadline_arm(&out->base, fixture->now + liveness_timeout);
    return out;
}

static bool dummy_publish_done(const cy_future_t* const base)
{
    (void)base;
    return false;
}

static cy_err_t dummy_publish_error(const cy_future_t* const base)
{
    (void)base;
    return CY_OK;
}

static void dummy_publish_timeout(cy_future_t* const base, const cy_us_t scheduled, const cy_us_t now)
{
    (void)base;
    (void)scheduled;
    (void)now;
}

static void dummy_publish_dispose(cy_future_t* const base)
{
    g_dummy_publish_dispose_count++;
    mem_free(base->cy, base);
}

static const cy_future_vtable_t dummy_publish_vtable = {
    .done    = dummy_publish_done,
    .error   = dummy_publish_error,
    .timeout = dummy_publish_timeout,
    .dispose = dummy_publish_dispose,
};

static cy_future_t* dummy_publish_new(cy_t* const cy)
{
    dummy_publish_future_t* const out = future_new(cy, &dummy_publish_vtable, sizeof(dummy_publish_future_t));
    TEST_ASSERT_NOT_NULL(out);
    return &out->base;
}

static request_future_remote_t* request_remote_find(const request_future_t* const fut, const uint64_t remote_id)
{
    return (request_future_remote_t*)cavl2_find(fut->remote_by_id, &remote_id, request_future_remote_cavl_compare);
}

static cy_breadcrumb_t make_test_breadcrumb(const fixture_t* const fixture,
                                            const uint64_t         remote_id,
                                            const cy_prio_t        priority,
                                            const uint64_t         topic_hash,
                                            const uint64_t         message_tag,
                                            const uint64_t         seqno)
{
    return (cy_breadcrumb_t){
        .cy          = (cy_t*)&fixture->cy,
        .priority    = priority,
        .remote_id   = remote_id,
        .topic_hash  = topic_hash,
        .message_tag = message_tag,
        .seqno       = seqno,
        .unicast_ctx = make_lane(remote_id).ctx,
    };
}

static cy_message_t* make_response_control_message(fixture_t* const fixture,
                                                   const byte_t     type,
                                                   const byte_t     tag,
                                                   const uint64_t   seqno,
                                                   const uint64_t   topic_hash,
                                                   const uint64_t   message_tag)
{
    TEST_ASSERT_TRUE(seqno <= SEQNO48_MASK);
    byte_t wire[HEADER_BYTES] = { type, tag };
    (void)serialize_u48(&wire[2], seqno);
    (void)serialize_u64(&wire[8], topic_hash);
    (void)serialize_u64(&wire[16], message_tag);
    return cy_test_message_make(&fixture->heap, wire, sizeof(wire));
}

static void dispatch_response_control(fixture_t* const fixture,
                                      const byte_t     type,
                                      const byte_t     tag,
                                      const uint64_t   seqno,
                                      const uint64_t   topic_hash,
                                      const uint64_t   message_tag,
                                      const uint64_t   remote_id,
                                      const cy_us_t    timestamp,
                                      const bool       multicast)
{
    cy_message_t* const msg = make_response_control_message(fixture, type, tag, seqno, topic_hash, message_tag);
    TEST_ASSERT_NOT_NULL(msg);
    cy_message_ts_t message = { .timestamp = timestamp, .content = msg };
    const cy_lane_t lane    = make_lane(remote_id);
    if (multicast) {
        const uint32_t      subject_id   = 1U;
        cy_subject_reader_t broad_reader = { .subject_id = 2U };
        fixture->cy.broad_reader         = &broad_reader;
        cy_on_message(&fixture->platform, lane, &subject_id, message);
        fixture->cy.broad_reader = NULL;
    } else {
        cy_on_message(&fixture->platform, lane, NULL, message);
    }
}

static void request_callback(cy_future_t* const fut)
{
    callback_capture_t* const cap = (callback_capture_t*)cy_future_context(fut).ptr[0];
    TEST_ASSERT_NOT_NULL(cap);
    cap->count++;
    cap->last_done  = cy_future_done(fut);
    cap->last_error = cy_future_error(fut);
}

static void test_respond_reliable_argument_validation(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const cy_bytes_t ok  = { .size = 0U, .data = NULL, .next = NULL };
    const cy_bytes_t bad = { .size = 1U, .data = NULL, .next = NULL };
    TEST_ASSERT_NULL(cy_respond_reliable(NULL, fixture.now + 1, ok));

    cy_breadcrumb_t invalid = { 0 };
    TEST_ASSERT_NULL(cy_respond_reliable(&invalid, fixture.now + 1, ok));
    invalid.cy = &fixture.cy;
    TEST_ASSERT_NULL(cy_respond_reliable(&invalid, -1, ok));
    TEST_ASSERT_NULL(cy_respond_reliable(&invalid, fixture.now + 1, bad));
    memset(&invalid.priority, 0, sizeof(invalid.priority));
    {
        const uint8_t bad_priority = UINT8_MAX;
        memcpy(&invalid.priority, &bad_priority, sizeof(bad_priority));
    }
    TEST_ASSERT_NULL(cy_respond_reliable(&invalid, fixture.now + 1, ok));

    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_initial_send_failure_returns_null(void)
{
    fixture_t fixture;
    fixture_init(&fixture);
    fixture.unicast_send_result = CY_ERR_MEDIA;

    cy_breadcrumb_t breadcrumb =
      make_test_breadcrumb(&fixture, UINT64_C(0xAA01), cy_prio_exceptional, UINT64_C(0x1234), UINT64_C(0x5678), 0U);
    const cy_bytes_t msg = { .size = 1U, .data = "A", .next = NULL };
    TEST_ASSERT_NULL(cy_respond_reliable(&breadcrumb, fixture.now + (10 * KILO), msg));
    TEST_ASSERT_EQUAL_size_t(1U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT64(1U, breadcrumb.seqno);
    TEST_ASSERT_NULL(fixture.cy.respond_futures_by_tag);

    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_ack_success(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t  remote_id   = UINT64_C(0xAA02);
    const uint64_t  topic_hash  = UINT64_C(0x1122334455667788);
    const uint64_t  message_tag = UINT64_C(0x8877665544332211);
    cy_breadcrumb_t breadcrumb =
      make_test_breadcrumb(&fixture, remote_id, cy_prio_exceptional, topic_hash, message_tag, 3U);
    const cy_bytes_t msg = { .size = 1U, .data = "B", .next = NULL };

    cy_future_t* const fut = cy_respond_reliable(&breadcrumb, fixture.now + (80 * KILO), msg);
    TEST_ASSERT_NOT_NULL(fut);
    TEST_ASSERT_EQUAL_UINT64(4U, breadcrumb.seqno);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_rel, fixture.last_unicast[0]);
    TEST_ASSERT_EQUAL_UINT64(3U, deserialize_u48(&fixture.last_unicast[2]));
    const byte_t tag = fixture.last_unicast[1];

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, 3U, topic_hash, message_tag, remote_id, fixture.now + 1, false);
    TEST_ASSERT_TRUE(cy_future_done(fut));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(fut));
    cy_future_destroy(fut);

    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_nack_failure(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t  remote_id   = UINT64_C(0xAA03);
    const uint64_t  topic_hash  = UINT64_C(0x1010);
    const uint64_t  message_tag = UINT64_C(0x2020);
    cy_breadcrumb_t breadcrumb =
      make_test_breadcrumb(&fixture, remote_id, cy_prio_exceptional, topic_hash, message_tag, 9U);
    const cy_bytes_t msg = { .size = 1U, .data = "C", .next = NULL };

    cy_future_t* const fut = cy_respond_reliable(&breadcrumb, fixture.now + (80 * KILO), msg);
    TEST_ASSERT_NOT_NULL(fut);
    const byte_t tag = fixture.last_unicast[1];

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_nack, tag, 9U, topic_hash, message_tag, remote_id, fixture.now + 1, false);
    TEST_ASSERT_TRUE(cy_future_done(fut));
    TEST_ASSERT_EQUAL_INT(CY_ERR_NACK, cy_future_error(fut));
    cy_future_destroy(fut);

    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_timeout_failure(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_breadcrumb_t breadcrumb =
      make_test_breadcrumb(&fixture, UINT64_C(0xAA04), cy_prio_exceptional, UINT64_C(0x3030), UINT64_C(0x4040), 0U);
    const cy_bytes_t msg = { .size = 1U, .data = "D", .next = NULL };

    const cy_us_t      deadline = fixture.now + (8 * KILO); // one-shot
    cy_future_t* const fut      = cy_respond_reliable(&breadcrumb, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.unicast_send_count);
    fixture_advance_to(&fixture, deadline + 1);
    TEST_ASSERT_TRUE(cy_future_done(fut));
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cy_future_error(fut));
    TEST_ASSERT_EQUAL_size_t(1U, fixture.unicast_send_count);
    cy_future_destroy(fut);

    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_retransmit_then_ack(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const cy_prio_t    prio       = cy_prio_exceptional;
    const cy_us_t      ack_to     = derive_ack_timeout(fixture.cy.ack_baseline_timeout, prio);
    const uint64_t     remote_id  = UINT64_C(0xAA05);
    const uint64_t     hash       = UINT64_C(0x5050);
    const uint64_t     msg_tag    = UINT64_C(0x6060);
    cy_breadcrumb_t    breadcrumb = make_test_breadcrumb(&fixture, remote_id, prio, hash, msg_tag, 2U);
    const cy_bytes_t   msg        = { .size = 1U, .data = "E", .next = NULL };
    const cy_us_t      deadline   = fixture.now + (5 * ack_to);
    cy_future_t* const fut        = cy_respond_reliable(&breadcrumb, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.unicast_send_count);
    const byte_t tag = fixture.last_unicast[1];

    fixture_advance_to(&fixture, fixture.now + ack_to + 1);
    TEST_ASSERT_FALSE(cy_future_done(fut));
    TEST_ASSERT_EQUAL_size_t(2U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_rel, fixture.last_unicast[0]);

    dispatch_response_control(&fixture, (byte_t)header_rsp_ack, tag, 2U, hash, msg_tag, remote_id, fixture.now, false);
    TEST_ASSERT_TRUE(cy_future_done(fut));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(fut));
    cy_future_destroy(fut);

    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_cancel_ignores_late_ack(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t   remote_id  = UINT64_C(0xAA06);
    const uint64_t   hash       = UINT64_C(0x7070);
    const uint64_t   msg_tag    = UINT64_C(0x8080);
    cy_breadcrumb_t  breadcrumb = make_test_breadcrumb(&fixture, remote_id, cy_prio_exceptional, hash, msg_tag, 4U);
    const cy_bytes_t msg        = { .size = 1U, .data = "F", .next = NULL };

    cy_future_t* const fut = cy_respond_reliable(&breadcrumb, fixture.now + (100 * KILO), msg);
    TEST_ASSERT_NOT_NULL(fut);
    const byte_t tag = fixture.last_unicast[1];
    cy_future_destroy(fut);
    TEST_ASSERT_NULL(fixture.cy.respond_futures_by_tag);

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, 4U, hash, msg_tag, remote_id, fixture.now + 1, false);
    TEST_ASSERT_NULL(fixture.cy.respond_futures_by_tag);
    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_mismatched_ack_ignored(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t   remote_id  = UINT64_C(0xAA07);
    const uint64_t   hash       = UINT64_C(0x9090);
    const uint64_t   msg_tag    = UINT64_C(0xA0A0);
    cy_breadcrumb_t  breadcrumb = make_test_breadcrumb(&fixture, remote_id, cy_prio_exceptional, hash, msg_tag, 5U);
    const cy_bytes_t msg        = { .size = 1U, .data = "G", .next = NULL };

    cy_future_t* const fut = cy_respond_reliable(&breadcrumb, fixture.now + (80 * KILO), msg);
    TEST_ASSERT_NOT_NULL(fut);
    const byte_t tag = fixture.last_unicast[1];

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, 5U, hash, msg_tag, remote_id + 1U, fixture.now + 1, false);
    TEST_ASSERT_FALSE(cy_future_done(fut));

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, 5U, hash, msg_tag, remote_id, fixture.now + 2, false);
    TEST_ASSERT_TRUE(cy_future_done(fut));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(fut));
    cy_future_destroy(fut);

    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_ack_match_field_mismatch_keeps_future_pending(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t   remote_id  = UINT64_C(0xAA07112233445566);
    const uint64_t   hash       = UINT64_C(0x1122334455667788);
    const uint64_t   msg_tag    = UINT64_C(0x8877665544332211);
    const uint64_t   seqno      = UINT64_C(0x123456789ABC) & SEQNO48_MASK;
    cy_breadcrumb_t  breadcrumb = make_test_breadcrumb(&fixture, remote_id, cy_prio_exceptional, hash, msg_tag, seqno);
    const cy_bytes_t msg        = { .size = 1U, .data = "Z", .next = NULL };

    cy_future_t* const fut_base = cy_respond_reliable(&breadcrumb, fixture.now + (80 * KILO), msg);
    TEST_ASSERT_NOT_NULL(fut_base);
    respond_future_t* const fut = (respond_future_t*)fut_base;
    const byte_t            tag = fixture.last_unicast[1];

    const uint64_t original_remote_id   = fut->breadcrumb.remote_id;
    const uint64_t original_message_tag = fut->breadcrumb.message_tag;
    const uint64_t original_topic_hash  = fut->breadcrumb.topic_hash;
    const uint64_t original_seqno       = fut->breadcrumb.seqno;
    const byte_t   original_tag         = fut->tag;

    fut->breadcrumb.remote_id = original_remote_id ^ UINT64_C(1);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, seqno, hash, msg_tag, remote_id, fixture.now + 1, false);
    TEST_ASSERT_FALSE(cy_future_done(fut_base));
    fut->breadcrumb.remote_id = original_remote_id;

    fut->breadcrumb.message_tag = original_message_tag ^ UINT64_C(1);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, seqno, hash, msg_tag, remote_id, fixture.now + 2, false);
    TEST_ASSERT_FALSE(cy_future_done(fut_base));
    fut->breadcrumb.message_tag = original_message_tag;

    fut->breadcrumb.topic_hash = original_topic_hash ^ UINT64_C(1);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, seqno, hash, msg_tag, remote_id, fixture.now + 3, false);
    TEST_ASSERT_FALSE(cy_future_done(fut_base));
    fut->breadcrumb.topic_hash = original_topic_hash;

    fut->breadcrumb.seqno = (original_seqno + 1U) & SEQNO48_MASK;
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, seqno, hash, msg_tag, remote_id, fixture.now + 4, false);
    TEST_ASSERT_FALSE(cy_future_done(fut_base));
    fut->breadcrumb.seqno = original_seqno;

    fut->tag = (original_tag == 0xFFU) ? 0xFEU : (byte_t)(original_tag + 1U);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, seqno, hash, msg_tag, remote_id, fixture.now + 5, false);
    TEST_ASSERT_FALSE(cy_future_done(fut_base));
    fut->tag = original_tag;

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, seqno, hash, msg_tag, remote_id, fixture.now + 6, false);
    TEST_ASSERT_TRUE(cy_future_done(fut_base));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(fut_base));
    cy_future_destroy(fut_base);

    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_key_collision_increments_tag(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t   remote_id    = UINT64_C(0xAA08);
    const uint64_t   hash         = UINT64_C(0xB0B0);
    const uint64_t   response_key = UINT64_C(0xC0C0);
    cy_breadcrumb_t  b1  = make_test_breadcrumb(&fixture, remote_id, cy_prio_exceptional, hash, response_key, 0U);
    cy_breadcrumb_t  b2  = make_test_breadcrumb(&fixture, remote_id, cy_prio_exceptional, hash, response_key, 0U);
    const cy_bytes_t msg = { .size = 1U, .data = "H", .next = NULL };

    cy_future_t* const fut1 = cy_respond_reliable(&b1, fixture.now + (80 * KILO), msg);
    TEST_ASSERT_NOT_NULL(fut1);
    const byte_t tag1 = fixture.last_unicast[1];

    cy_future_t* const fut2 = cy_respond_reliable(&b2, fixture.now + (80 * KILO), msg);
    TEST_ASSERT_NOT_NULL(fut2);
    const byte_t tag2 = fixture.last_unicast[1];
    TEST_ASSERT_TRUE(tag1 != tag2);
    TEST_ASSERT_EQUAL_UINT64(1U, b1.seqno);
    TEST_ASSERT_EQUAL_UINT64(1U, b2.seqno);

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag1, 0U, hash, response_key, remote_id, fixture.now + 1, false);
    TEST_ASSERT_TRUE(cy_future_done(fut1));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(fut1));

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag2, 0U, hash, response_key, remote_id, fixture.now + 2, false);
    TEST_ASSERT_TRUE(cy_future_done(fut2));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(fut2));

    cy_future_destroy(fut1);
    cy_future_destroy(fut2);
    fixture_assert_clean(&fixture);
}

static void test_respond_reliable_multicast_ack_rejected(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t   remote_id  = UINT64_C(0xAA09);
    const uint64_t   hash       = UINT64_C(0xD0D0);
    const uint64_t   msg_tag    = UINT64_C(0xE0E0);
    cy_breadcrumb_t  breadcrumb = make_test_breadcrumb(&fixture, remote_id, cy_prio_exceptional, hash, msg_tag, 1U);
    const cy_bytes_t msg        = { .size = 1U, .data = "I", .next = NULL };

    cy_future_t* const fut = cy_respond_reliable(&breadcrumb, fixture.now + (80 * KILO), msg);
    TEST_ASSERT_NOT_NULL(fut);
    const byte_t tag = fixture.last_unicast[1];

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, 1U, hash, msg_tag, remote_id, fixture.now + 1, true);
    TEST_ASSERT_FALSE(cy_future_done(fut));
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_ack, tag, 1U, hash, msg_tag, remote_id, fixture.now + 2, false);
    TEST_ASSERT_TRUE(cy_future_done(fut));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(fut));
    cy_future_destroy(fut);

    fixture_assert_clean(&fixture);
}

static void test_message_refcount_primitives_destroy_once(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const byte_t        payload[2] = { 0xAAU, 0xBBU };
    cy_message_t* const msg        = cy_test_message_make(&fixture.heap, payload, sizeof(payload));
    TEST_ASSERT_NOT_NULL(msg);
    TEST_ASSERT_EQUAL_UINT32(1U, msg->refcount);
    assert_message_counters(0U, 1U);

    cy_message_refcount_inc(NULL); // NULL-safe no-op.
    cy_message_refcount_dec(NULL); // NULL-safe no-op.
    TEST_ASSERT_EQUAL_UINT32(1U, msg->refcount);
    assert_message_counters(0U, 1U);

    cy_message_refcount_inc(msg);
    TEST_ASSERT_EQUAL_UINT32(2U, msg->refcount);
    assert_message_counters(0U, 1U);

    cy_message_refcount_dec(msg);
    TEST_ASSERT_EQUAL_UINT32(1U, msg->refcount);
    assert_message_counters(0U, 1U);

    cy_message_refcount_dec(msg);
    assert_message_counters(1U, 0U);
    fixture_assert_clean(&fixture);
}

static void test_request_on_response_best_effort_overwrite_and_callback(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t         topic;
    request_future_t*  fut = make_request_future(&fixture, &topic, UINT64_C(1001), 25000);
    callback_capture_t cap = { 0 };
    cy_future_context_set(&fut->base, (cy_user_context_t){ { &cap } });
    cy_future_callback_set(&fut->base, request_callback);
    const size_t callback_base = cap.count;

    const cy_lane_t lane_a = make_lane(42U);
    const cy_lane_t lane_b = make_lane(99U);

    const cy_message_ts_t first = make_message(&fixture, fixture.now + 10U, 1U);
    TEST_ASSERT_TRUE(request_on_response(fut, 7U, first, false, lane_a));
    TEST_ASSERT_EQUAL_size_t(callback_base + 1U, cap.count);
    TEST_ASSERT_TRUE(cap.last_done);
    TEST_ASSERT_EQUAL_INT(CY_OK, cap.last_error);
    TEST_ASSERT_EQUAL_UINT64(1U, fut->response_count);
    TEST_ASSERT_EQUAL_UINT64(42U, fut->last_response.remote_id);
    TEST_ASSERT_EQUAL_UINT64(7U, fut->last_response.seqno);
    TEST_ASSERT_TRUE(future_deadline_armed(&fut->base));
    TEST_ASSERT_EQUAL_UINT32(2U, first.content->refcount);
    cy_message_refcount_dec(first.content); // release local copy
    assert_message_counters(0U, 1U);

    const cy_message_ts_t second = make_message(&fixture, fixture.now + 20U, 2U);
    TEST_ASSERT_TRUE(request_on_response(fut, 0U, second, false, lane_b));
    TEST_ASSERT_EQUAL_size_t(callback_base + 2U, cap.count);
    TEST_ASSERT_TRUE(cap.last_done);
    TEST_ASSERT_EQUAL_INT(CY_OK, cap.last_error);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count);
    TEST_ASSERT_EQUAL_UINT64(99U, fut->last_response.remote_id);
    TEST_ASSERT_EQUAL_UINT64(0U, fut->last_response.seqno);
    cy_message_refcount_dec(second.content); // release local copy
    assert_message_counters(1U, 1U);         // Overwrite destroys the first response.

    const cy_response_t moved = cy_response_move(&fut->base);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    TEST_ASSERT_FALSE(cy_future_done(&fut->base));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(&fut->base));
    cy_message_refcount_dec(moved.message.content);
    assert_message_counters(2U, 0U);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    assert_message_counters(2U, 0U);
    fixture_assert_clean(&fixture);
}

static void test_request_future_destroy_releases_last_response(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut  = make_request_future(&fixture, &topic, UINT64_C(1101), 20000);
    const cy_lane_t   lane = make_lane(77U);

    const cy_message_ts_t msg = make_message(&fixture, fixture.now + 5U, 0x31U);
    TEST_ASSERT_TRUE(request_on_response(fut, 1U, msg, false, lane));
    cy_message_refcount_dec(msg.content); // release local copy
    assert_message_counters(0U, 1U);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    assert_message_counters(1U, 0U);
    fixture_assert_clean(&fixture);
}

static void test_request_future_dispose_zombie_releases_last_response_early(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut  = make_request_future(&fixture, &topic, UINT64_C(1102), 20000);
    const cy_lane_t   lane = make_lane(88U);

    const cy_message_ts_t msg = make_message(&fixture, fixture.now + 6U, 0x41U);
    TEST_ASSERT_TRUE(request_on_response(fut, 9U, msg, true, lane)); // reliable creates remote state.
    cy_message_refcount_dec(msg.content);                            // release local copy
    assert_message_counters(0U, 1U);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_TRUE(fut->finalized);
    TEST_ASSERT_NULL(fut->last_response.message.content);
    TEST_ASSERT_NOT_NULL(topic.request_futures_by_tag);
    assert_message_counters(1U, 0U); // dispose() released the retained response immediately.

    fixture_advance_to(&fixture, fixture.now + (SESSION_LIFETIME / 2) + 1);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    assert_message_counters(1U, 0U);
    fixture_assert_clean(&fixture);
}

static void test_request_on_response_reliable_dedup_and_ordering(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut  = make_request_future(&fixture, &topic, UINT64_C(1002), 20000);
    const cy_lane_t   lane = make_lane(123U);

    cy_message_ts_t msg = make_message(&fixture, fixture.now + 1U, 10U);
    TEST_ASSERT_TRUE(request_on_response(fut, 300U, msg, true, lane));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(1U, fut->response_count);

    request_future_remote_t* const remote = request_remote_find(fut, lane.id);
    TEST_ASSERT_NOT_NULL(remote);
    TEST_ASSERT_EQUAL_UINT64(300U, remote->seqno_top);
    TEST_ASSERT_TRUE(bitmap_test(remote->seqno_acked, 0U));

    msg = make_message(&fixture, fixture.now + 2U, 11U);
    TEST_ASSERT_TRUE(request_on_response(fut, 300U, msg, true, lane)); // duplicate
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(1U, fut->response_count);

    msg = make_message(&fixture, fixture.now + 3U, 12U);
    TEST_ASSERT_TRUE(request_on_response(fut, 299U, msg, true, lane)); // out-of-order new
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count);
    TEST_ASSERT_TRUE(bitmap_test(remote->seqno_acked, 1U));

    msg = make_message(&fixture, fixture.now + 4U, 13U);
    TEST_ASSERT_TRUE(request_on_response(fut, 299U, msg, true, lane)); // duplicate
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count);

    msg = make_message(&fixture, fixture.now + 5U, 14U);
    TEST_ASSERT_FALSE(request_on_response(fut, 108U, msg, true, lane)); // too old for history window
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count);

    cy_future_destroy(&fut->base); // becomes zombie because remote states exist
    TEST_ASSERT_NOT_NULL(topic.request_futures_by_tag);
    fixture_advance_to(&fixture, fixture.now + (SESSION_LIFETIME / 2) + 1);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    fixture_assert_clean(&fixture);
}

static void test_request_on_response_zombie_ack_seen_nack_unseen(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut  = make_request_future(&fixture, &topic, UINT64_C(1003), 20000);
    const cy_lane_t   lane = make_lane(555U);

    cy_message_ts_t msg = make_message(&fixture, fixture.now + 1U, 20U);
    TEST_ASSERT_TRUE(request_on_response(fut, 5U, msg, true, lane));
    cy_message_refcount_dec(msg.content);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_NOT_NULL(topic.request_futures_by_tag);
    TEST_ASSERT_TRUE(fut->finalized);
    TEST_ASSERT_NULL(fut->last_response.message.content);
    TEST_ASSERT_TRUE(future_deadline_armed(&fut->base));

    msg = make_message(&fixture, fixture.now + 2U, 21U);
    TEST_ASSERT_TRUE(request_on_response(fut, 5U, msg, true, lane)); // seen -> ack
    cy_message_refcount_dec(msg.content);

    msg = make_message(&fixture, fixture.now + 3U, 22U);
    TEST_ASSERT_FALSE(request_on_response(fut, 6U, msg, true, lane)); // unseen -> nack
    cy_message_refcount_dec(msg.content);

    msg = make_message(&fixture, fixture.now + 4U, 23U);
    TEST_ASSERT_FALSE(request_on_response(fut, 4U, msg, true, lane)); // unseen older -> nack
    cy_message_refcount_dec(msg.content);

    msg = make_message(&fixture, fixture.now + 5U, 24U);
    TEST_ASSERT_FALSE(request_on_response(fut, 0U, msg, false, lane)); // best-effort in zombie mode -> reject
    cy_message_refcount_dec(msg.content);

    fixture_advance_to(&fixture, fixture.now + (SESSION_LIFETIME / 2) + 1);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    fixture_assert_clean(&fixture);
}

static void test_request_on_response_reliable_oom_escalates_failure(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t         topic;
    request_future_t*  fut = make_request_future(&fixture, &topic, UINT64_C(1004), 20000);
    callback_capture_t cap = { 0 };
    cy_future_context_set(&fut->base, (cy_user_context_t){ { &cap } });
    cy_future_callback_set(&fut->base, request_callback);
    future_deadline_arm(&fut->base, fixture.now + 500000);
    TEST_ASSERT_TRUE(future_deadline_armed(&fut->base));

    cy_message_ts_t msg = make_message(&fixture, fixture.now + 10U, 30U);
    fixture_set_fail_after(&fixture, 0U); // first new allocation fails (remote state)
    TEST_ASSERT_FALSE(request_on_response(fut, 0U, msg, true, make_lane(1000U)));
    cy_message_refcount_dec(msg.content);

    TEST_ASSERT_EQUAL_size_t(1U, cap.count);
    TEST_ASSERT_TRUE(cap.last_done);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, cap.last_error);
    TEST_ASSERT_FALSE(future_deadline_armed(&fut->base));
    TEST_ASSERT_EQUAL_size_t(1U, fixture.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, fixture.last_async_error);
    TEST_ASSERT_TRUE(cy_future_done(&fut->base));
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, cy_future_error(&fut->base));

    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    fixture_assert_clean(&fixture);
}

static void test_request_future_dispose_destroys_publish_and_removes_index(void)
{
    fixture_t fixture;
    fixture_init(&fixture);
    g_dummy_publish_dispose_count = 0U;

    cy_topic_t        topic;
    request_future_t* fut = make_request_future(&fixture, &topic, UINT64_C(1005), 20000);
    fut->publish          = dummy_publish_new(&fixture.cy);
    future_deadline_arm(&fut->base, fixture.now + 1000U);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_EQUAL_size_t(1U, g_dummy_publish_dispose_count);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    fixture_assert_clean(&fixture);
}

static void test_request_publish_callback_pending_update_noop(void)
{
    fixture_t fixture;
    fixture_init(&fixture);
    g_dummy_publish_dispose_count = 0U;

    cy_topic_t        topic;
    request_future_t* fut = make_request_future(&fixture, &topic, UINT64_C(1006), 20000);
    fut->publish          = dummy_publish_new(&fixture.cy);
    cy_future_context_set(fut->publish, (cy_user_context_t){ { fut } });
    future_deadline_arm(&fut->base, fixture.now + 1000U);
    TEST_ASSERT_TRUE(future_deadline_armed(&fut->base));

    request_publish_callback(fut->publish); // pending status branch: no state change expected

    TEST_ASSERT_NOT_NULL(fut->publish);
    TEST_ASSERT_FALSE(fut->finalized);
    TEST_ASSERT_TRUE(future_deadline_armed(&fut->base));
    TEST_ASSERT_NOT_NULL(topic.request_futures_by_tag);
    TEST_ASSERT_EQUAL_size_t(0U, g_dummy_publish_dispose_count);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_EQUAL_size_t(1U, g_dummy_publish_dispose_count);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    fixture_assert_clean(&fixture);
}

static void test_send_response_ack_serialization(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const cy_lane_t lane = make_lane(0xAABBCCDDEEFF0011ULL);

    send_response_ack(&fixture.cy,
                      lane,
                      UINT64_C(0x0102030405060708),
                      UINT64_C(0x0000123456789ABC),
                      0x5AU,
                      UINT64_C(0x1122334455667788),
                      true,
                      fixture.now + 100U);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_size_t(HEADER_BYTES, fixture.last_unicast_size);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, fixture.last_unicast[0]);
    TEST_ASSERT_EQUAL_UINT8(0x5AU, fixture.last_unicast[1]);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x0000123456789ABC), deserialize_u48(&fixture.last_unicast[2]));
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x1122334455667788), deserialize_u64(&fixture.last_unicast[8]));
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x0102030405060708), deserialize_u64(&fixture.last_unicast[16]));

    send_response_ack(&fixture.cy,
                      lane,
                      UINT64_C(0xFFEEDDCCBBAA0099),
                      UINT64_C(0x0000000000000007),
                      0x17U,
                      UINT64_C(0x8877665544332211),
                      false,
                      fixture.now + 200U);
    TEST_ASSERT_EQUAL_size_t(2U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_size_t(HEADER_BYTES, fixture.last_unicast_size);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, fixture.last_unicast[0]);
    TEST_ASSERT_EQUAL_UINT8(0x17U, fixture.last_unicast[1]);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x0000000000000007), deserialize_u48(&fixture.last_unicast[2]));
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x8877665544332211), deserialize_u64(&fixture.last_unicast[8]));
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0xFFEEDDCCBBAA0099), deserialize_u64(&fixture.last_unicast[16]));

    fixture_assert_clean(&fixture);
}

void setUp(void)
{
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
    cy_test_message_reset_counters();
}

void tearDown(void) { TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count()); }

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_respond_reliable_argument_validation);
    RUN_TEST(test_respond_reliable_initial_send_failure_returns_null);
    RUN_TEST(test_respond_reliable_ack_success);
    RUN_TEST(test_respond_reliable_nack_failure);
    RUN_TEST(test_respond_reliable_timeout_failure);
    RUN_TEST(test_respond_reliable_retransmit_then_ack);
    RUN_TEST(test_respond_reliable_cancel_ignores_late_ack);
    RUN_TEST(test_respond_reliable_mismatched_ack_ignored);
    RUN_TEST(test_respond_reliable_ack_match_field_mismatch_keeps_future_pending);
    RUN_TEST(test_respond_reliable_key_collision_increments_tag);
    RUN_TEST(test_respond_reliable_multicast_ack_rejected);
    RUN_TEST(test_message_refcount_primitives_destroy_once);
    RUN_TEST(test_request_on_response_best_effort_overwrite_and_callback);
    RUN_TEST(test_request_future_destroy_releases_last_response);
    RUN_TEST(test_request_future_dispose_zombie_releases_last_response_early);
    RUN_TEST(test_request_on_response_reliable_dedup_and_ordering);
    RUN_TEST(test_request_on_response_zombie_ack_seen_nack_unseen);
    RUN_TEST(test_request_on_response_reliable_oom_escalates_failure);
    RUN_TEST(test_request_future_dispose_destroys_publish_and_removes_index);
    RUN_TEST(test_request_publish_callback_pending_update_noop);
    RUN_TEST(test_send_response_ack_serialization);
    return UNITY_END();
}
