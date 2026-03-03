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
    cy_err_t  p2p_send_result;
    size_t    p2p_send_count;
    cy_lane_t last_lane;
    cy_us_t   last_deadline;
    byte_t    last_p2p[HEADER_BYTES];
    size_t    last_p2p_size;

    size_t   async_error_count;
    cy_err_t last_async_error;
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

static cy_err_t fixture_p2p_send(cy_platform_t* const   platform,
                                 const cy_lane_t* const lane,
                                 const cy_us_t          deadline,
                                 const cy_bytes_t       message)
{
    fixture_t* const self = (fixture_t*)platform;
    self->p2p_send_count++;
    if (lane != NULL) {
        self->last_lane = *lane;
    } else {
        memset(&self->last_lane, 0, sizeof(self->last_lane));
    }
    self->last_deadline = deadline;
    self->last_p2p_size = 0U;
    memset(self->last_p2p, 0, sizeof(self->last_p2p));
    for (const cy_bytes_t* seg = &message; seg != NULL; seg = seg->next) {
        if ((seg->size > 0U) && (seg->data != NULL) && (self->last_p2p_size < sizeof(self->last_p2p))) {
            const size_t copy_size = smaller(seg->size, sizeof(self->last_p2p) - self->last_p2p_size);
            memcpy(&self->last_p2p[self->last_p2p_size], seg->data, copy_size);
            self->last_p2p_size += copy_size;
        }
    }
    return self->p2p_send_result;
}

static void fixture_on_async_error(cy_t* const       cy,
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

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0xD9A1F26E3984C57B));
    self->platform.vtable             = &self->vtable;
    self->platform.subject_id_modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    self->platform.cy                 = &self->cy;
    self->vtable.realloc              = fixture_realloc;
    self->vtable.p2p_send             = fixture_p2p_send;
    self->vtable.p2p_extent_set       = fixture_p2p_extent_set;
    self->vtable.spin                 = fixture_spin;
    self->vtable.now                  = fixture_now;
    self->vtable.random               = fixture_random;
    self->cy.platform                 = &self->platform;
    self->cy.async_error_handler      = fixture_on_async_error;
    olga_init(&self->cy.olga, &self->cy, olga_now);
    self->fail_after        = SIZE_MAX;
    self->new_alloc_count   = 0U;
    self->now               = 10000;
    self->random_state      = UINT64_C(0x123456789ABCDEF0);
    self->p2p_send_result   = CY_OK;
    self->last_async_error  = CY_OK;
    self->last_deadline     = BIG_BANG;
    self->last_p2p_size     = 0U;
    self->async_error_count = 0U;
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
    memcpy(lane.p2p.state, &lane.id, smaller(sizeof(lane.p2p.state), sizeof(lane.id)));
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

static void request_callback(cy_future_t* const fut)
{
    callback_capture_t* const cap = (callback_capture_t*)cy_future_context(fut).ptr[0];
    TEST_ASSERT_NOT_NULL(cap);
    cap->count++;
    cap->last_done  = cy_future_done(fut);
    cap->last_error = cy_future_error(fut);
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

    const cy_message_ts_t second = make_message(&fixture, fixture.now + 20U, 2U);
    TEST_ASSERT_TRUE(request_on_response(fut, 0U, second, false, lane_b));
    TEST_ASSERT_EQUAL_size_t(callback_base + 2U, cap.count);
    TEST_ASSERT_TRUE(cap.last_done);
    TEST_ASSERT_EQUAL_INT(CY_OK, cap.last_error);
    TEST_ASSERT_EQUAL_UINT64(2U, fut->response_count);
    TEST_ASSERT_EQUAL_UINT64(99U, fut->last_response.remote_id);
    TEST_ASSERT_EQUAL_UINT64(0U, fut->last_response.seqno);
    cy_message_refcount_dec(second.content); // release local copy

    const cy_response_t moved = cy_response(&fut->base);
    TEST_ASSERT_NOT_NULL(moved.message.content);
    TEST_ASSERT_FALSE(cy_future_done(&fut->base));
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_future_error(&fut->base));
    cy_message_refcount_dec(moved.message.content);

    cy_future_destroy(&fut->base);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
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
    TEST_ASSERT_EQUAL_size_t(1U, fixture.p2p_send_count);
    TEST_ASSERT_EQUAL_size_t(HEADER_BYTES, fixture.last_p2p_size);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_ack, fixture.last_p2p[0]);
    TEST_ASSERT_EQUAL_UINT8(0x5AU, fixture.last_p2p[1]);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x0000123456789ABC), deserialize_u48(&fixture.last_p2p[2]));
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x1122334455667788), deserialize_u64(&fixture.last_p2p[8]));
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x0102030405060708), deserialize_u64(&fixture.last_p2p[16]));

    send_response_ack(&fixture.cy,
                      lane,
                      UINT64_C(0xFFEEDDCCBBAA0099),
                      UINT64_C(0x0000000000000007),
                      0x17U,
                      UINT64_C(0x8877665544332211),
                      false,
                      fixture.now + 200U);
    TEST_ASSERT_EQUAL_size_t(2U, fixture.p2p_send_count);
    TEST_ASSERT_EQUAL_size_t(HEADER_BYTES, fixture.last_p2p_size);
    TEST_ASSERT_EQUAL_UINT8(header_rsp_nack, fixture.last_p2p[0]);
    TEST_ASSERT_EQUAL_UINT8(0x17U, fixture.last_p2p[1]);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x0000000000000007), deserialize_u48(&fixture.last_p2p[2]));
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0x8877665544332211), deserialize_u64(&fixture.last_p2p[8]));
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(0xFFEEDDCCBBAA0099), deserialize_u64(&fixture.last_p2p[16]));

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
    RUN_TEST(test_request_on_response_best_effort_overwrite_and_callback);
    RUN_TEST(test_request_on_response_reliable_dedup_and_ordering);
    RUN_TEST(test_request_on_response_zombie_ack_seen_nack_unseen);
    RUN_TEST(test_request_on_response_reliable_oom_escalates_failure);
    RUN_TEST(test_request_future_dispose_destroys_publish_and_removes_index);
    RUN_TEST(test_request_publish_callback_pending_update_noop);
    RUN_TEST(test_send_response_ack_serialization);
    return UNITY_END();
}
