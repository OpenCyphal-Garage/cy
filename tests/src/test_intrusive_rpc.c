#define CY_CONFIG_REQUEST_ACK_RETENTION_us 7000000LL
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

    size_t fail_size;
    size_t fail_size_skip;  // Matching allocations to let through before failing; both promotion allocations
    size_t fail_size_count; // are the same size, so failing only the second one requires a skip.

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

static_assert(sizeof(request_ack_t) != sizeof(request_future_remote_t), "size-keyed OOM injection is ambiguous");

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    fixture_t* const self = (fixture_t*)platform;
    if ((ptr == NULL) && (size > 0U)) {
        if ((self->fail_size_count > 0U) && (self->fail_size == size)) {
            if (self->fail_size_skip > 0U) {
                self->fail_size_skip--;
            } else {
                self->fail_size_count--;
                return NULL;
            }
        }
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

static void fixture_diag_async_error(cy_diag_t* const  diag,
                                     cy_topic_t* const topic,
                                     const cy_err_t    error,
                                     const uint16_t    line_number)
{
    (void)topic;
    (void)line_number;
    fixture_t* const self = (fixture_t*)diag->user_context.ptr[0];
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
    self->diag = (cy_diag_t){ .next = NULL, .user_context = CY_USER_CONTEXT_EMPTY, .vtable = &fixture_diag_vtable };
    self->diag.user_context.ptr[0] = self;
    cy_diag_add(&self->cy, &self->diag);
    olga_init(&self->cy.olga, &self->cy, olga_now);
    self->cy.ack_baseline_timeout = ACK_BASELINE_DEFAULT_TIMEOUT_us;
    self->now                     = 10000;
    self->random_state            = UINT64_C(0x123456789ABCDEF0);
    self->unicast_send_result     = CY_OK;
    self->last_async_error        = CY_OK;
    self->last_deadline           = BIG_BANG;
    self->last_unicast_size       = 0U;
    self->async_error_count       = 0U;
}

static void fixture_fail_alloc_size_after(fixture_t* const self,
                                          const size_t     size,
                                          const size_t     skip,
                                          const size_t     count)
{
    self->fail_size       = size;
    self->fail_size_skip  = skip;
    self->fail_size_count = count;
}

static void fixture_fail_alloc_size(fixture_t* const self, const size_t size, const size_t count)
{
    fixture_fail_alloc_size_after(self, size, 0U, count);
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
    out->ack                             = NULL;
    const bool insert_ok                 = future_index_insert(&out->base, &topic->request_futures_by_tag, key);
    TEST_ASSERT_TRUE(insert_ok);
    future_deadline_arm(&out->base, fixture->now + liveness_timeout);
    return out;
}

static request_future_t* make_indexed_request_future(fixture_t* const  fixture,
                                                     cy_topic_t* const topic,
                                                     const uint64_t    key,
                                                     const cy_us_t     liveness_timeout,
                                                     const uint64_t    topic_hash)
{
    request_future_t* const out     = make_request_future(fixture, topic, key, liveness_timeout);
    topic->hash                     = topic_hash;
    const cy_tree_t* const inserted = cavl2_find_or_insert(
      &fixture->cy.topics_by_hash, &topic->hash, cavl_comp_topic_hash, topic, cavl2_trivial_factory);
    TEST_ASSERT_EQUAL_PTR(&topic->index_hash, inserted);
    return out;
}

static void unindex_request_topic(fixture_t* const fixture, cy_topic_t* const topic)
{
    cavl2_remove_if(&fixture->cy.topics_by_hash, &topic->index_hash);
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

// Returns the promoted per-remote node, or NULL if there is no record yet or it is still in the inlined solo shape.
// Use request_ack_is_solo() to assert the solo shape positively rather than inferring it from a NULL here.
static request_future_remote_t* request_remote_find(const request_future_t* const fut, const uint64_t remote_id)
{
    if ((fut->ack == NULL) || fut->ack->solo) {
        return NULL;
    }
    return (request_future_remote_t*)cavl2_find(fut->ack->u.tree, &remote_id, request_future_remote_cavl_compare);
}

static bool request_ack_is_solo(const request_future_t* const fut, const uint64_t remote_id)
{
    return (fut->ack != NULL) && fut->ack->solo && (fut->ack->u.solo_remote_id == remote_id);
}

// The intrusive fixture drives olga directly and never runs poll(), so retained records are never swept for us.
// This is strictly beyond any record retained at or before the fixture's current time.
static void reap_request_acks(const fixture_t* const fixture, cy_topic_t* const topic)
{
    request_ack_drop_stale(topic, fixture->now + (CY_CONFIG_REQUEST_ACK_RETENTION_us) + 1);
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

static void test_respond_argument_validation(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const cy_bytes_t ok  = { .size = 0U, .data = NULL, .next = NULL };
    const cy_bytes_t bad = { .size = 4U, .data = NULL, .next = NULL };
    cy_breadcrumb_t  breadcrumb =
      make_test_breadcrumb(&fixture, UINT64_C(0xAA00), cy_prio_nominal, UINT64_C(0x1234), UINT64_C(0x5678), 11U);

    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_respond(NULL, fixture.now + 1, ok));
    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_respond(&breadcrumb, -1, ok));

    cy_breadcrumb_t invalid = breadcrumb;
    invalid.cy              = NULL;
    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_respond(&invalid, fixture.now + 1, ok));

    invalid = breadcrumb;
    {
        const uint8_t bad_priority = UINT8_MAX;
        memset(&invalid.priority, 0, sizeof(invalid.priority));
        memcpy(&invalid.priority, &bad_priority, sizeof(bad_priority));
    }
    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_respond(&invalid, fixture.now + 1, ok));
    TEST_ASSERT_EQUAL_size_t(0U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT64(11U, invalid.seqno);

    TEST_ASSERT_EQUAL_INT(CY_ERR_ARGUMENT, cy_respond(&breadcrumb, fixture.now + 1, bad));
    TEST_ASSERT_EQUAL_size_t(0U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT64(11U, breadcrumb.seqno);

    TEST_ASSERT_EQUAL_INT(CY_OK, cy_respond(&breadcrumb, fixture.now + 2, ok));
    TEST_ASSERT_EQUAL_size_t(1U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT64(12U, breadcrumb.seqno);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_be, fixture.last_unicast[0]);
    TEST_ASSERT_EQUAL_UINT64(11U, deserialize_u48(&fixture.last_unicast[2]));

    fixture_assert_clean(&fixture);
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
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 7U, first, false, lane_a));
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
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, second, false, lane_b));
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
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 1U, msg, false, lane));
    cy_message_refcount_dec(msg.content); // release local copy
    assert_message_counters(0U, 1U);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    assert_message_counters(1U, 0U);
    fixture_assert_clean(&fixture);
}

static void test_request_future_dispose_hands_over_and_releases_last_response(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut  = make_request_future(&fixture, &topic, UINT64_C(1102), 20000);
    const cy_lane_t   lane = make_lane(88U);

    const cy_message_ts_t msg = make_message(&fixture, fixture.now + 6U, 0x41U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 9U, msg, true, lane)); // creates the ack record
    cy_message_refcount_dec(msg.content);                                                  // release local copy
    assert_message_counters(0U, 1U);
    TEST_ASSERT_NOT_NULL(fut->ack);

    // The future is freed outright; the record is handed to the topic. Nothing of `fut` may be read after this.
    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    TEST_ASSERT_NOT_NULL(topic.request_acks_by_tag);
    TEST_ASSERT_NOT_NULL(topic.request_acks_by_expiry.head);
    assert_message_counters(1U, 0U); // dispose() released the retained response immediately.

    // seqno 9 was the first response from this remote, so the record is promoted, not solo.
    const request_ack_t* const ack = (const request_ack_t*)topic.request_acks_by_tag;
    TEST_ASSERT_FALSE(ack->solo);
    TEST_ASSERT_EQUAL_INT64(fixture.now + (CY_CONFIG_REQUEST_ACK_RETENTION_us), ack->dead_at);

    reap_request_acks(&fixture, &topic);
    TEST_ASSERT_NULL(topic.request_acks_by_tag);
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
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 300U, msg, true, lane));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(1U, fut->response_count);

    request_future_remote_t* const remote = request_remote_find(fut, lane.id);
    TEST_ASSERT_NOT_NULL(remote);
    TEST_ASSERT_EQUAL_UINT64(300U, remote->seqno_top);
    TEST_ASSERT_TRUE(bitmap_test(remote->seqno_acked, 0U));

    msg = make_message(&fixture, fixture.now + 2U, 11U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 300U, msg, true, lane)); // duplicate
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(1U, fut->response_count);

    msg = make_message(&fixture, fixture.now + 3U, 12U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 299U, msg, true, lane)); // out-of-order new
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count);
    TEST_ASSERT_TRUE(bitmap_test(remote->seqno_acked, 1U));

    msg = make_message(&fixture, fixture.now + 4U, 13U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 299U, msg, true, lane)); // duplicate
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count);

    msg = make_message(&fixture, fixture.now + 5U, 14U);
    TEST_ASSERT_EQUAL_INT(response_rx_nack, request_on_response(fut, 108U, msg, true, lane)); // too old
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count);

    cy_future_destroy(&fut->base); // hands over the ack record because reliable responses were acked
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    TEST_ASSERT_NOT_NULL(topic.request_acks_by_tag);
    reap_request_acks(&fixture, &topic);
    TEST_ASSERT_NULL(topic.request_acks_by_tag);
    fixture_assert_clean(&fixture);
}

// After the future is gone the retained record answers, and it is query-only: it must never insert a remote,
// never shift a bitmap and never set a bit.
static void test_request_ack_record_ack_seen_nack_unseen(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t    topic_hash  = UINT64_C(0x5150515051505150);
    const uint64_t    message_tag = UINT64_C(1003);
    const uint64_t    remote_id   = 555U;
    cy_topic_t        topic;
    request_future_t* fut = make_indexed_request_future(&fixture, &topic, message_tag, 20000, topic_hash);

    cy_message_ts_t msg = make_message(&fixture, fixture.now + 1U, 20U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 5U, msg, true, make_lane(remote_id)));
    cy_message_refcount_dec(msg.content);

    cy_future_destroy(&fut->base); // `fut` is freed here; only the record survives.
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    TEST_ASSERT_NOT_NULL(topic.request_acks_by_tag);
    request_ack_t* const ack = (request_ack_t*)topic.request_acks_by_tag;

    TEST_ASSERT_TRUE(request_ack_test(ack, remote_id, 5U));  // seen -> ack
    TEST_ASSERT_FALSE(request_ack_test(ack, remote_id, 6U)); // above the frontier -> nack
    TEST_ASSERT_FALSE(request_ack_test(ack, remote_id, 4U)); // below the frontier, never acked -> nack
    TEST_ASSERT_FALSE(request_ack_test(ack, 556U, 5U));      // unknown remote -> nack

    request_future_remote_t* const remote = (request_future_remote_t*)ack->u.tree;
    TEST_ASSERT_NOT_NULL(remote);

    // Same verdicts through the real wire path, including the best-effort case which emits nothing, and one
    // dispatch from a remote the record has never seen -- the case that would insert a node if the path mutated.
    const size_t sent_before = fixture.unicast_send_count;
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, 0x11U, 5U, topic_hash, message_tag, remote_id, fixture.now + 2U, false);
    TEST_ASSERT_EQUAL_size_t(sent_before + 1U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, fixture.last_unicast[0]);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, 0x12U, 6U, topic_hash, message_tag, remote_id, fixture.now + 3U, false);
    TEST_ASSERT_EQUAL_size_t(sent_before + 2U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, fixture.last_unicast[0]);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, 0x14U, 0U, topic_hash, message_tag, 556U, fixture.now + 4U, false);
    TEST_ASSERT_EQUAL_size_t(sent_before + 3U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, fixture.last_unicast[0]);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_be, 0x13U, 0U, topic_hash, message_tag, remote_id, fixture.now + 5U, false);
    TEST_ASSERT_EQUAL_size_t(sent_before + 3U, fixture.unicast_send_count); // best-effort: no control frame at all

    // Query-only: after everything above, including the unknown-remote dispatch, the record is unchanged.
    TEST_ASSERT_FALSE(ack->solo);
    TEST_ASSERT_EQUAL_PTR(remote, (request_future_remote_t*)ack->u.tree);
    TEST_ASSERT_NULL(cavl2_next_greater(&remote->index_by_remote_id)); // remote 556 was not inserted
    TEST_ASSERT_NULL(remote->index_by_remote_id.lr[0]);                // ...on either side
    TEST_ASSERT_EQUAL_UINT64(5U, remote->seqno_top);                   // frontier not advanced by seqno 6
    TEST_ASSERT_TRUE(bitmap_test(remote->seqno_acked, 0U));
    TEST_ASSERT_FALSE(bitmap_test(remote->seqno_acked, 1U)); // seqno 4 did not set a bit

    reap_request_acks(&fixture, &topic);
    TEST_ASSERT_NULL(topic.request_acks_by_tag);
    unindex_request_topic(&fixture, &topic);
    fixture_assert_clean(&fixture);
}

// A single responder whose first reliable response carries seqno 0 is stored inline: no tree node, no bitmap,
// no second allocation. This is the shape the whole optimization exists for.
static void test_request_ack_solo_claim_and_duplicate(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut  = make_request_future(&fixture, &topic, UINT64_C(2001), 20000);
    const cy_lane_t   lane = make_lane(0xA1U);

    cy_message_ts_t msg          = make_message(&fixture, fixture.now + 1U, 1U);
    const size_t    frags_before = guarded_heap_allocated_fragments(&fixture.heap);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, lane));
    const size_t frags_after = guarded_heap_allocated_fragments(&fixture.heap);
    cy_message_refcount_dec(msg.content); // release before asserting so a failure cannot leak into tearDown
    TEST_ASSERT_EQUAL_size_t(frags_before + 1U, frags_after); // the record only -- no per-remote node
    TEST_ASSERT_TRUE(request_ack_is_solo(fut, lane.id));
    TEST_ASSERT_EQUAL_UINT64(1U, fut->response_count);

    // A duplicate of seqno 0 is acked straight from the inlined slot and must not promote.
    msg = make_message(&fixture, fixture.now + 2U, 2U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, lane));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_TRUE(request_ack_is_solo(fut, lane.id));
    TEST_ASSERT_EQUAL_UINT64(1U, fut->response_count); // deduplicated, the app saw it once

    // Both NACK branches of the retained solo shape. Neither is reachable through the promoted shape, and line
    // coverage cannot distinguish them from the ACK case above because they share the return statement.
    cy_future_destroy(&fut->base);
    const request_ack_t* const ack = (const request_ack_t*)topic.request_acks_by_tag;
    TEST_ASSERT_NOT_NULL(ack);
    TEST_ASSERT_TRUE(ack->solo);
    TEST_ASSERT_TRUE(request_ack_test(ack, lane.id, 0U));       // the inlined ack
    TEST_ASSERT_FALSE(request_ack_test(ack, lane.id, 1U));      // right remote, wrong seqno
    TEST_ASSERT_FALSE(request_ack_test(ack, lane.id + 1U, 0U)); // wrong remote, right seqno

    reap_request_acks(&fixture, &topic);
    fixture_assert_clean(&fixture);
}

// Promotion by the same remote must reconstruct the inlined ack losslessly: seqno 0's bit is shifted to index s.
static void test_request_ack_solo_promotes_same_remote(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut  = make_request_future(&fixture, &topic, UINT64_C(2002), 20000);
    const cy_lane_t   lane = make_lane(0xA2U);

    cy_message_ts_t msg = make_message(&fixture, fixture.now + 1U, 1U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, lane));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_TRUE(request_ack_is_solo(fut, lane.id));

    msg = make_message(&fixture, fixture.now + 2U, 2U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 3U, msg, true, lane));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_FALSE(request_ack_is_solo(fut, lane.id));
    const request_future_remote_t* const remote = request_remote_find(fut, lane.id);
    TEST_ASSERT_NOT_NULL(remote);
    TEST_ASSERT_EQUAL_UINT64(3U, remote->seqno_top);
    TEST_ASSERT_TRUE(bitmap_test(remote->seqno_acked, 0U)); // seqno 3
    TEST_ASSERT_TRUE(bitmap_test(remote->seqno_acked, 3U)); // seqno 0, carried across the shift
    TEST_ASSERT_FALSE(bitmap_test(remote->seqno_acked, 1U));
    TEST_ASSERT_FALSE(bitmap_test(remote->seqno_acked, 2U));

    // The original seqno-0 ack is still honoured after promotion.
    msg = make_message(&fixture, fixture.now + 3U, 3U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, lane));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count); // seqno 0 and 3 only

    cy_future_destroy(&fut->base);
    reap_request_acks(&fixture, &topic);
    fixture_assert_clean(&fixture);
}

// A second responder promotes too. The solo remote is migrated FIRST so that a failure on the second
// allocation cannot lose its ack.
static void test_request_ack_solo_promotes_second_remote(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut = make_request_future(&fixture, &topic, UINT64_C(2003), 20000);
    const cy_lane_t   r   = make_lane(0xA3U);
    const cy_lane_t   s   = make_lane(0xB3U);

    cy_message_ts_t msg = make_message(&fixture, fixture.now + 1U, 1U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, r));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_TRUE(request_ack_is_solo(fut, r.id));

    msg = make_message(&fixture, fixture.now + 2U, 2U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, s));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_FALSE(request_ack_is_solo(fut, r.id));

    const request_future_remote_t* const rr = request_remote_find(fut, r.id);
    const request_future_remote_t* const ss = request_remote_find(fut, s.id);
    TEST_ASSERT_NOT_NULL(rr);
    TEST_ASSERT_NOT_NULL(ss);
    TEST_ASSERT_EQUAL_UINT64(0U, rr->seqno_top);
    TEST_ASSERT_TRUE(bitmap_test(rr->seqno_acked, 0U)); // the migrated solo ack
    TEST_ASSERT_EQUAL_UINT64(0U, ss->seqno_top);
    TEST_ASSERT_TRUE(bitmap_test(ss->seqno_acked, 0U));

    // Both remotes' seqno-0 acks survive.
    msg = make_message(&fixture, fixture.now + 3U, 3U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, r));
    cy_message_refcount_dec(msg.content);
    msg = make_message(&fixture, fixture.now + 4U, 4U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, s));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_NOT_NULL(topic.request_acks_by_tag);
    reap_request_acks(&fixture, &topic); // must drain BOTH remote nodes, not just the record
    fixture_assert_clean(&fixture);
}

// bitmap_shift() resets the whole bitmap when the jump is >= REQUEST_FUTURE_HISTORY. 191 keeps the old ack,
// 192 drops it. This is the shift-side boundary, distinct from the receive-side dist>=192 rejection.
static void test_request_ack_shift_boundary_191_192(void)
{
    for (unsigned k = 0; k < 2U; k++) {
        const uint64_t jump   = (k == 0U) ? (REQUEST_FUTURE_HISTORY - 1U) : REQUEST_FUTURE_HISTORY;
        const bool     expect = (k == 0U); // 191 -> still acked; 192 -> forgotten
        fixture_t      fixture;
        fixture_init(&fixture);

        cy_topic_t        topic;
        request_future_t* fut  = make_request_future(&fixture, &topic, UINT64_C(2004) + k, 20000);
        const cy_lane_t   lane = make_lane(0xA4U);

        cy_message_ts_t msg = make_message(&fixture, fixture.now + 1U, 1U);
        TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, lane));
        cy_message_refcount_dec(msg.content);

        msg = make_message(&fixture, fixture.now + 2U, 2U);
        TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, jump, msg, true, lane));
        cy_message_refcount_dec(msg.content);
        const request_future_remote_t* const remote = request_remote_find(fut, lane.id);
        TEST_ASSERT_NOT_NULL(remote);
        TEST_ASSERT_EQUAL_UINT64(jump, remote->seqno_top);
        TEST_ASSERT_EQUAL_INT(expect, bitmap_test_bounded(remote->seqno_acked, REQUEST_FUTURE_HISTORY, jump));

        msg = make_message(&fixture, fixture.now + 3U, 3U);
        TEST_ASSERT_EQUAL_INT(expect ? response_rx_ack : response_rx_nack,
                              request_on_response(fut, 0U, msg, true, lane));
        cy_message_refcount_dec(msg.content);

        cy_future_destroy(&fut->base);
        reap_request_acks(&fixture, &topic);
        fixture_assert_clean(&fixture);
    }
}

// Every allocation-failure exit reports exactly one async error, leaves the liveness deadline untouched, and
// preserves whatever was already acked. Retrying after each partial failure must converge.
static void test_request_ack_promotion_oom_preserves_state(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut = make_request_future(&fixture, &topic, UINT64_C(2010), 20000);
    const cy_lane_t   r   = make_lane(0xA5U);
    const cy_lane_t   s   = make_lane(0xB5U);

    cy_message_ts_t msg = make_message(&fixture, fixture.now + 1U, 1U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, r));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_TRUE(request_ack_is_solo(fut, r.id));
    const cy_us_t deadline_base = fut->base.timeout.deadline;

    // (a) Same-remote promotion fails on the reconstruction allocation -> silent, still solo, ack intact.
    fixture_fail_alloc_size(&fixture, sizeof(request_future_remote_t), 1U);
    msg = make_message(&fixture, fixture.now + 2U, 2U);
    TEST_ASSERT_EQUAL_INT(response_rx_silent, request_on_response(fut, 7U, msg, true, r));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_size_t(0U, fixture.fail_size_count);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, fixture.last_async_error);
    TEST_ASSERT_TRUE(request_ack_is_solo(fut, r.id));
    TEST_ASSERT_EQUAL_INT64(deadline_base, fut->base.timeout.deadline); // liveness not extended by a dropped response
    TEST_ASSERT_EQUAL_UINT64(1U, fut->response_count);

    // (b) Second-remote promotion fails while reconstructing the solo node -> silent, still solo.
    fixture_fail_alloc_size(&fixture, sizeof(request_future_remote_t), 1U);
    msg = make_message(&fixture, fixture.now + 3U, 3U);
    TEST_ASSERT_EQUAL_INT(response_rx_silent, request_on_response(fut, 0U, msg, true, s));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_size_t(0U, fixture.fail_size_count);
    TEST_ASSERT_EQUAL_size_t(2U, fixture.async_error_count);
    TEST_ASSERT_TRUE(request_ack_is_solo(fut, r.id));

    // (c) Second-remote node fails AFTER the solo node was reconstructed -> silent, record promoted,
    //     and the solo remote's ack survives losslessly. The naive migration order would lose it here.
    fixture_fail_alloc_size_after(&fixture, sizeof(request_future_remote_t), 1U, 1U);
    msg = make_message(&fixture, fixture.now + 4U, 4U);
    TEST_ASSERT_EQUAL_INT(response_rx_silent, request_on_response(fut, 0U, msg, true, s));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_size_t(0U, fixture.fail_size_count);
    TEST_ASSERT_EQUAL_size_t(3U, fixture.async_error_count);
    TEST_ASSERT_FALSE(request_ack_is_solo(fut, r.id)); // partial promotion persists
    const request_future_remote_t* const rr = request_remote_find(fut, r.id);
    TEST_ASSERT_NOT_NULL(rr);
    TEST_ASSERT_TRUE(bitmap_test(rr->seqno_acked, 0U)); // R's seqno-0 ack preserved across the failure
    TEST_ASSERT_NULL(request_remote_find(fut, s.id));

    // (d) Retry after the partial promotion converges, and R's original ack is still honoured.
    msg = make_message(&fixture, fixture.now + 5U, 5U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, s));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_NOT_NULL(request_remote_find(fut, s.id));
    msg = make_message(&fixture, fixture.now + 6U, 6U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fut, 0U, msg, true, r)); // duplicate -> ack
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count); // R@0 and S@0

    cy_future_destroy(&fut->base);
    reap_request_acks(&fixture, &topic);
    fixture_assert_clean(&fixture);
}

// A first reliable response with seqno > 0 needs two allocations. If the remote node fails after the record
// was allocated, the record is left in the NONE state, which answers NACK and is NOT retained at disposal.
static void test_request_ack_none_state_not_retained(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut  = make_request_future(&fixture, &topic, UINT64_C(2011), 20000);
    const cy_lane_t   lane = make_lane(0xA6U);

    fixture_fail_alloc_size(&fixture, sizeof(request_future_remote_t), 1U);
    cy_message_ts_t msg = make_message(&fixture, fixture.now + 1U, 1U);
    TEST_ASSERT_EQUAL_INT(response_rx_silent, request_on_response(fut, 5U, msg, true, lane)); // seqno > 0
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_size_t(0U, fixture.fail_size_count);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.async_error_count);
    TEST_ASSERT_NOT_NULL(fut->ack); // the record was allocated...
    TEST_ASSERT_FALSE(fut->ack->solo);
    TEST_ASSERT_NULL(fut->ack->u.tree); // ...and is in the NONE state
    TEST_ASSERT_FALSE(request_ack_test(fut->ack, lane.id, 5U));

    // A NONE record can only ever answer NACK, so disposal frees it instead of retaining it.
    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    TEST_ASSERT_NULL(topic.request_acks_by_tag);
    TEST_ASSERT_NULL(topic.request_acks_by_expiry.head);
    fixture_assert_clean(&fixture);
}

// The expiry list is re-headed only at handoff, so it stays sorted by dead_at even when futures are disposed
// in a different order than their first responses arrived. The tail sweep depends on that.
static void test_request_ack_expiry_order_follows_disposal(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic_a;
    cy_topic_t        topic_b;
    request_future_t* fa = make_request_future(&fixture, &topic_a, UINT64_C(2020), 20000);
    // Both records must live on the same topic for a single expiry list, so re-point the second future.
    request_future_t* fb = make_request_future(&fixture, &topic_b, UINT64_C(2021), 20000);
    future_index_remove(&fb->base, &topic_b.request_futures_by_tag);
    fb->topic            = &topic_a;
    const bool insert_ok = future_index_insert(&fb->base, &topic_a.request_futures_by_tag, UINT64_C(2021));
    TEST_ASSERT_TRUE(insert_ok);

    cy_message_ts_t msg = make_message(&fixture, fixture.now + 1U, 1U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fa, 0U, msg, true, make_lane(0xC1U)));
    cy_message_refcount_dec(msg.content);
    msg = make_message(&fixture, fixture.now + 2U, 2U);
    TEST_ASSERT_EQUAL_INT(response_rx_ack, request_on_response(fb, 0U, msg, true, make_lane(0xC2U)));
    cy_message_refcount_dec(msg.content);

    // Dispose in the reverse order and advance the clock in between, so dead_at differs.
    cy_future_destroy(&fb->base);
    fixture_advance_to(&fixture, fixture.now + 1000);
    cy_future_destroy(&fa->base);

    // Head is the most recent handoff (fa), tail is the oldest (fb) -- i.e. sorted by dead_at ascending at the tail.
    const request_ack_t* const head = LIST_MEMBER(topic_a.request_acks_by_expiry.head, request_ack_t, expiry);
    const request_ack_t* const tail = LIST_MEMBER(topic_a.request_acks_by_expiry.tail, request_ack_t, expiry);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(2020), head->tag);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(2021), tail->tag);
    TEST_ASSERT_TRUE(tail->dead_at < head->dead_at);

    // Sweeping at a time between the two deadlines must reap only the older one.
    request_ack_drop_stale(&topic_a, tail->dead_at + 1);
    TEST_ASSERT_NOT_NULL(topic_a.request_acks_by_tag);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(2020),
                             LIST_MEMBER(topic_a.request_acks_by_expiry.tail, request_ack_t, expiry)->tag);

    reap_request_acks(&fixture, &topic_a);
    TEST_ASSERT_NULL(topic_a.request_acks_by_tag);
    fixture_assert_clean(&fixture);
}

static void test_request_on_response_reliable_oom_stays_pending_silent(void)
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
    const size_t  callback_base = cap.count;
    const cy_us_t deadline_base = fut->base.timeout.deadline;

    // seqno 0 is the first response from this remote, so it takes the solo path: the only allocation is the
    // ack record itself. Failing sizeof(request_future_remote_t) here would not fire at all.
    cy_message_ts_t msg = make_message(&fixture, fixture.now + 10U, 30U);
    fixture_fail_alloc_size(&fixture, sizeof(request_ack_t), 1U);
    TEST_ASSERT_EQUAL_INT(response_rx_silent, request_on_response(fut, 0U, msg, true, make_lane(1000U)));
    cy_message_refcount_dec(msg.content);
    TEST_ASSERT_EQUAL_size_t(0U, fixture.fail_size_count); // the injection was consumed, not absorbed elsewhere

    TEST_ASSERT_EQUAL_size_t(callback_base, cap.count);
    TEST_ASSERT_TRUE(future_deadline_armed(&fut->base));
    TEST_ASSERT_EQUAL_INT64(deadline_base, fut->base.timeout.deadline);
    TEST_ASSERT_EQUAL_UINT64(0U, fut->response_count);
    TEST_ASSERT_NULL(fut->ack);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, fixture.last_async_error);
    TEST_ASSERT_FALSE(cy_future_done(&fut->base));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(&fut->base));

    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    fixture_assert_clean(&fixture);
}

static void test_response_wire_reliable_oom_silent_then_retransmit(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t topic_hash  = UINT64_C(0xABCD123456789ABC);
    const uint64_t message_tag = UINT64_C(0x1122334455667788);
    const uint64_t remote_id   = UINT64_C(0xA5A5000000000001);
    const byte_t   tag         = 0x6CU;
    const uint64_t seqno       = 0U;

    cy_topic_t         topic;
    request_future_t*  fut = make_indexed_request_future(&fixture, &topic, message_tag, 20000, topic_hash);
    callback_capture_t cap = { 0 };
    cy_future_context_set(&fut->base, (cy_user_context_t){ { &cap } });
    cy_future_callback_set(&fut->base, request_callback);
    const size_t  callback_base = cap.count;
    const cy_us_t deadline_base = fut->base.timeout.deadline;

    // seqno is 0, so this is the solo path and the ack record is the only allocation on it.
    fixture_fail_alloc_size(&fixture, sizeof(request_ack_t), 1U);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, tag, seqno, topic_hash, message_tag, remote_id, fixture.now + 10U, false);
    TEST_ASSERT_EQUAL_size_t(0U, fixture.fail_size_count); // the injection was consumed, not absorbed elsewhere
    TEST_ASSERT_EQUAL_size_t(0U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_size_t(callback_base, cap.count);
    TEST_ASSERT_EQUAL_UINT64(0U, fut->response_count);
    TEST_ASSERT_NULL(fut->ack);
    TEST_ASSERT_TRUE(future_deadline_armed(&fut->base));
    TEST_ASSERT_EQUAL_INT64(deadline_base, fut->base.timeout.deadline);
    TEST_ASSERT_FALSE(cy_future_done(&fut->base));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(&fut->base));
    TEST_ASSERT_EQUAL_size_t(1U, fixture.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, fixture.last_async_error);

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, tag, seqno, topic_hash, message_tag, remote_id, fixture.now + 20U, false);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, fixture.last_unicast[0]);
    TEST_ASSERT_EQUAL_UINT8(tag, fixture.last_unicast[1]);
    TEST_ASSERT_EQUAL_UINT64(seqno, deserialize_u48(&fixture.last_unicast[2]));
    TEST_ASSERT_EQUAL_UINT64(topic_hash, deserialize_u64(&fixture.last_unicast[8]));
    TEST_ASSERT_EQUAL_UINT64(message_tag, deserialize_u64(&fixture.last_unicast[16]));
    TEST_ASSERT_EQUAL_size_t(callback_base + 1U, cap.count);
    TEST_ASSERT_TRUE(cy_future_done(&fut->base));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(&fut->base));
    TEST_ASSERT_EQUAL_UINT64(1U, fut->response_count);

    cy_response_t moved = cy_response_move(&fut->base);
    TEST_ASSERT_EQUAL_UINT64(remote_id, moved.remote_id);
    TEST_ASSERT_EQUAL_UINT64(seqno, moved.seqno);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    TEST_ASSERT_EQUAL_size_t(0U, cy_message_size(moved.message.content));
    cy_message_refcount_dec(moved.message.content);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    TEST_ASSERT_NOT_NULL(topic.request_acks_by_tag);
    // The single responder answered seqno 0 first, so the record stays in the inlined solo shape: no tree node.
    TEST_ASSERT_TRUE(((const request_ack_t*)topic.request_acks_by_tag)->solo);

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, tag, seqno, topic_hash, message_tag, remote_id, fixture.now + 30U, false);
    TEST_ASSERT_EQUAL_size_t(2U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, fixture.last_unicast[0]);
    TEST_ASSERT_EQUAL_UINT8(tag, fixture.last_unicast[1]);
    TEST_ASSERT_EQUAL_UINT64(seqno, deserialize_u48(&fixture.last_unicast[2]));
    TEST_ASSERT_EQUAL_UINT64(topic_hash, deserialize_u64(&fixture.last_unicast[8]));
    TEST_ASSERT_EQUAL_UINT64(message_tag, deserialize_u64(&fixture.last_unicast[16]));

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, tag, seqno + 1U, topic_hash, message_tag, remote_id, fixture.now + 40U, false);
    TEST_ASSERT_EQUAL_size_t(3U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, fixture.last_unicast[0]);
    TEST_ASSERT_EQUAL_UINT8(tag, fixture.last_unicast[1]);
    TEST_ASSERT_EQUAL_UINT64(seqno + 1U, deserialize_u48(&fixture.last_unicast[2]));
    TEST_ASSERT_EQUAL_UINT64(topic_hash, deserialize_u64(&fixture.last_unicast[8]));
    TEST_ASSERT_EQUAL_UINT64(message_tag, deserialize_u64(&fixture.last_unicast[16]));

    // Retention is a floor: past dead_at the record still answers ACK until a sweep actually runs.
    fixture_advance_to(&fixture, fixture.now + (CY_CONFIG_REQUEST_ACK_RETENTION_us) + 1);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, tag, seqno, topic_hash, message_tag, remote_id, fixture.now + 50U, false);
    TEST_ASSERT_EQUAL_size_t(4U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, fixture.last_unicast[0]);

    reap_request_acks(&fixture, &topic);
    TEST_ASSERT_NULL(topic.request_acks_by_tag);
    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, tag, seqno, topic_hash, message_tag, remote_id, fixture.now + 60U, false);
    TEST_ASSERT_EQUAL_size_t(5U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, fixture.last_unicast[0]); // record gone -> nack
    unindex_request_topic(&fixture, &topic);
    fixture_assert_clean(&fixture);
}

static void test_response_wire_reliable_client_gone_nacks(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const uint64_t topic_hash  = UINT64_C(0x0102030405060708);
    const uint64_t message_tag = UINT64_C(0x8877665544332211);
    const uint64_t remote_id   = UINT64_C(0xA5A5000000000002);
    const byte_t   tag         = 0x7DU;
    const uint64_t seqno       = 0U;

    cy_topic_t        topic;
    request_future_t* fut = make_indexed_request_future(&fixture, &topic, message_tag, 20000, topic_hash);
    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);

    dispatch_response_control(
      &fixture, (byte_t)header_rsp_rel, tag, seqno, topic_hash, message_tag, remote_id, fixture.now + 10U, false);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.unicast_send_count);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, fixture.last_unicast[0]);
    TEST_ASSERT_EQUAL_UINT8(tag, fixture.last_unicast[1]);
    TEST_ASSERT_EQUAL_UINT64(seqno, deserialize_u48(&fixture.last_unicast[2]));
    TEST_ASSERT_EQUAL_UINT64(topic_hash, deserialize_u64(&fixture.last_unicast[8]));
    TEST_ASSERT_EQUAL_UINT64(message_tag, deserialize_u64(&fixture.last_unicast[16]));

    unindex_request_topic(&fixture, &topic);
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
    TEST_ASSERT_NULL(fut->ack); // no response seen, so no deduplication state was created
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
    RUN_TEST(test_respond_argument_validation);
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
    RUN_TEST(test_request_future_dispose_hands_over_and_releases_last_response);
    RUN_TEST(test_request_on_response_reliable_dedup_and_ordering);
    RUN_TEST(test_request_ack_record_ack_seen_nack_unseen);
    RUN_TEST(test_request_ack_solo_claim_and_duplicate);
    RUN_TEST(test_request_ack_solo_promotes_same_remote);
    RUN_TEST(test_request_ack_solo_promotes_second_remote);
    RUN_TEST(test_request_ack_shift_boundary_191_192);
    RUN_TEST(test_request_ack_promotion_oom_preserves_state);
    RUN_TEST(test_request_ack_none_state_not_retained);
    RUN_TEST(test_request_ack_expiry_order_follows_disposal);
    RUN_TEST(test_request_on_response_reliable_oom_stays_pending_silent);
    RUN_TEST(test_response_wire_reliable_oom_silent_then_retransmit);
    RUN_TEST(test_response_wire_reliable_client_gone_nacks);
    RUN_TEST(test_request_future_dispose_destroys_publish_and_removes_index);
    RUN_TEST(test_request_publish_callback_pending_update_noop);
    RUN_TEST(test_send_response_ack_serialization);
    return UNITY_END();
}
