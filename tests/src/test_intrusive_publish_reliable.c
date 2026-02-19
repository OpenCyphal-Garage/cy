#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
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

    size_t   async_error_count;
    cy_err_t last_async_error;
    uint16_t last_async_error_line;

    cy_err_t p2p_send_result;
    size_t   p2p_send_count;
} fixture_t;

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

static cy_err_t fixture_p2p_send(cy_platform_t* const   platform,
                                 const cy_lane_t* const lane,
                                 const cy_us_t          deadline,
                                 const cy_bytes_t       message)
{
    (void)lane;
    (void)deadline;
    (void)message;
    fixture_t* const self = (fixture_t*)platform;
    self->p2p_send_count++;
    return self->p2p_send_result;
}

static void fixture_on_async_error(cy_t* const       cy,
                                   cy_topic_t* const topic,
                                   const cy_err_t    error,
                                   const uint16_t    line_number)
{
    (void)topic;
    fixture_t* const self = (fixture_t*)cy->platform;
    self->async_error_count++;
    self->last_async_error      = error;
    self->last_async_error_line = line_number;
}

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0xB17E5D0C1234ABCD));
    self->platform.vtable             = &self->vtable;
    self->platform.subject_id_modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    self->platform.cy                 = &self->cy;
    self->vtable.realloc              = fixture_realloc;
    self->vtable.p2p_send             = fixture_p2p_send;
    self->cy.platform                 = &self->platform;
    self->cy.async_error_handler      = fixture_on_async_error;
    self->fail_after                  = SIZE_MAX;
    self->new_alloc_count             = 0;
    self->last_async_error            = CY_OK;
    self->p2p_send_result             = CY_OK;
}

static void fixture_set_fail_after(fixture_t* const self, const size_t fail_after)
{
    self->fail_after      = fail_after;
    self->new_alloc_count = 0;
}

static void forget_associations(cy_topic_t* const topic)
{
    while (topic->assoc_by_remote_id != NULL) {
        association_t* const ass = CAVL2_TO_OWNER(cavl2_min(topic->assoc_by_remote_id), association_t, index_remote_id);
        TEST_ASSERT_NOT_NULL(ass);
        cavl2_remove(&topic->assoc_by_remote_id, &ass->index_remote_id);
        topic->assoc_count--;
        mem_free(topic->cy, ass);
    }
}

static void test_publish_future_is_last_attempt_basic(void)
{
    // (100 + 50*2) = 200 > 200 is FALSE
    TEST_ASSERT_FALSE(publish_future_is_last_attempt(100, 50, 200));
    // (100 + 50*2) = 200 > 199 is TRUE
    TEST_ASSERT_TRUE(publish_future_is_last_attempt(100, 50, 199));
    // (0 + 0*2) = 0 > 0 is FALSE
    TEST_ASSERT_FALSE(publish_future_is_last_attempt(0, 0, 0));
    // (0 + 1*2) = 2 > 1 is TRUE
    TEST_ASSERT_TRUE(publish_future_is_last_attempt(0, 1, 1));
}

static void test_is_last_attempt_exactly_equal(void)
{
    TEST_ASSERT_FALSE(publish_future_is_last_attempt(100, 50, 200));
}

static void test_is_last_attempt_one_over(void) { TEST_ASSERT_TRUE(publish_future_is_last_attempt(101, 50, 200)); }

static void test_is_last_attempt_large_margin(void)
{
    TEST_ASSERT_TRUE(publish_future_is_last_attempt(1000, 500, 100));
}

static void test_is_last_attempt_large_room(void) { TEST_ASSERT_FALSE(publish_future_is_last_attempt(100, 50, 10000)); }

static void test_is_last_attempt_zero_timeout(void)
{
    TEST_ASSERT_TRUE(publish_future_is_last_attempt(5, 0, 4));
    TEST_ASSERT_FALSE(publish_future_is_last_attempt(5, 0, 5));
}

static void test_is_last_attempt_preserves_full_ack_window(void)
{
    // Timeline from cy.c docs with total deadline 24:
    // t=10 initial attempt timeout=1  -> ack_deadline=11
    // t=11 retry #1       timeout=2  -> ack_deadline=13
    // t=13 retry #2       timeout=4  -> ack_deadline=17 (must be last)
    TEST_ASSERT_FALSE(publish_future_is_last_attempt(11, 1, 24));
    TEST_ASSERT_FALSE(publish_future_is_last_attempt(13, 2, 24));
    TEST_ASSERT_TRUE(publish_future_is_last_attempt(17, 4, 24));
}

static void test_bisect_empty(void) { TEST_ASSERT_EQUAL_size_t(0U, association_bisect(NULL, 0U, 123U)); }

static void test_bisect_single_match(void)
{
    association_t  ass[] = { { .remote_id = 42U } };
    association_t* ptr[] = { &ass[0] };
    TEST_ASSERT_EQUAL_size_t(0U, association_bisect(ptr, 1U, 42U));
}

static void test_bisect_single_miss_low(void)
{
    association_t  ass[] = { { .remote_id = 42U } };
    association_t* ptr[] = { &ass[0] };
    TEST_ASSERT_EQUAL_size_t(0U, association_bisect(ptr, 1U, 10U));
}

static void test_bisect_single_miss_high(void)
{
    association_t  ass[] = { { .remote_id = 42U } };
    association_t* ptr[] = { &ass[0] };
    TEST_ASSERT_EQUAL_size_t(1U, association_bisect(ptr, 1U, 100U));
}

static void test_bisect_multiple_first(void)
{
    association_t  ass[] = { { .remote_id = 10U }, { .remote_id = 20U }, { .remote_id = 30U } };
    association_t* ptr[] = { &ass[0], &ass[1], &ass[2] };
    TEST_ASSERT_EQUAL_size_t(0U, association_bisect(ptr, 3U, 10U));
}

static void test_bisect_multiple_last(void)
{
    association_t  ass[] = { { .remote_id = 10U }, { .remote_id = 20U }, { .remote_id = 30U } };
    association_t* ptr[] = { &ass[0], &ass[1], &ass[2] };
    TEST_ASSERT_EQUAL_size_t(2U, association_bisect(ptr, 3U, 30U));
}

static void test_bisect_multiple_middle(void)
{
    association_t  ass[] = { { .remote_id = 10U }, { .remote_id = 20U }, { .remote_id = 30U } };
    association_t* ptr[] = { &ass[0], &ass[1], &ass[2] };
    TEST_ASSERT_EQUAL_size_t(1U, association_bisect(ptr, 3U, 20U));
}

static void test_bisect_multiple_insert_point(void)
{
    association_t  ass[] = { { .remote_id = 10U }, { .remote_id = 20U }, { .remote_id = 30U } };
    association_t* ptr[] = { &ass[0], &ass[1], &ass[2] };
    TEST_ASSERT_EQUAL_size_t(2U, association_bisect(ptr, 3U, 25U));
}

static publish_future_t* make_publish_future_with_one_assoc(fixture_t* const      fixture,
                                                            cy_topic_t* const     topic,
                                                            cy_publisher_t* const pub,
                                                            association_t* const  ass,
                                                            const uint64_t        seqno)
{
    memset(topic, 0, sizeof(*topic));
    memset(pub, 0, sizeof(*pub));
    memset(ass, 0, sizeof(*ass));

    topic->cy                = &fixture->cy;
    topic->assoc_slack_limit = 2U;
    topic->pub_tag_baseline  = 100U;

    pub->topic = topic;

    ass->pending_count = 1U;

    publish_future_t* const fut =
      (publish_future_t*)mem_alloc_zero(&fixture->cy, sizeof(publish_future_t) + sizeof(association_t*));
    TEST_ASSERT_NOT_NULL(fut);
    fut->owner           = pub;
    fut->assoc_capacity  = 1U;
    fut->assoc_remaining = 1U;
    fut->base.key        = topic->pub_tag_baseline + seqno;
    fut->assoc_knockout  = bitmap_new(&fixture->cy, fut->assoc_capacity);
    TEST_ASSERT_NOT_NULL(fut->assoc_knockout);
    fut->assoc_set[0] = ass;
    return fut;
}

static void test_release_no_slack_when_premature(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t              topic;
    cy_publisher_t          pub;
    association_t           ass;
    publish_future_t* const fut = make_publish_future_with_one_assoc(&fixture, &topic, &pub, &ass, 10U);

    bitmap_set(fut->assoc_knockout, 0U);
    ass.seqno_witness = 10U;

    publish_future_release_associations(fut, true);

    TEST_ASSERT_EQUAL_size_t(0U, ass.slack);
    TEST_ASSERT_EQUAL_size_t(0U, ass.pending_count);
    TEST_ASSERT_EQUAL_size_t(0U, fut->assoc_capacity);
    TEST_ASSERT_NULL(fut->assoc_knockout);
    TEST_ASSERT_NULL(fut->assoc_set[0]);

    mem_free(&fixture.cy, fut);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_release_slack_incremented_when_conditions_met(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t              topic;
    cy_publisher_t          pub;
    association_t           ass;
    publish_future_t* const fut = make_publish_future_with_one_assoc(&fixture, &topic, &pub, &ass, 11U);

    bitmap_set(fut->assoc_knockout, 0U);
    ass.seqno_witness = 10U;

    publish_future_release_associations(fut, false);

    TEST_ASSERT_EQUAL_size_t(1U, ass.slack);
    TEST_ASSERT_EQUAL_size_t(0U, ass.pending_count);
    TEST_ASSERT_EQUAL_size_t(0U, fut->assoc_capacity);
    TEST_ASSERT_NULL(fut->assoc_knockout);
    TEST_ASSERT_NULL(fut->assoc_set[0]);

    mem_free(&fixture.cy, fut);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_release_no_slack_when_seqno_behind_witness(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t              topic;
    cy_publisher_t          pub;
    association_t           ass;
    publish_future_t* const fut = make_publish_future_with_one_assoc(&fixture, &topic, &pub, &ass, 9U);

    bitmap_set(fut->assoc_knockout, 0U);
    ass.seqno_witness = 10U;

    publish_future_release_associations(fut, false);

    TEST_ASSERT_EQUAL_size_t(0U, ass.slack);
    TEST_ASSERT_EQUAL_size_t(0U, ass.pending_count);
    TEST_ASSERT_EQUAL_size_t(0U, fut->assoc_capacity);
    TEST_ASSERT_NULL(fut->assoc_knockout);
    TEST_ASSERT_NULL(fut->assoc_set[0]);

    mem_free(&fixture.cy, fut);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_release_no_forget_when_pending_remains(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t              topic;
    cy_publisher_t          pub;
    association_t           ass;
    publish_future_t* const fut = make_publish_future_with_one_assoc(&fixture, &topic, &pub, &ass, 11U);

    bitmap_set(fut->assoc_knockout, 0U);
    ass.seqno_witness = 10U;
    ass.slack         = 1U;
    ass.pending_count = 2U;

    publish_future_release_associations(fut, false);

    TEST_ASSERT_EQUAL_size_t(2U, ass.slack);
    TEST_ASSERT_EQUAL_size_t(1U, ass.pending_count);
    TEST_ASSERT_EQUAL_size_t(0U, fut->assoc_capacity);
    TEST_ASSERT_NULL(fut->assoc_knockout);
    TEST_ASSERT_NULL(fut->assoc_set[0]);

    mem_free(&fixture.cy, fut);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_publish_future_cancel_done_is_noop(void)
{
    publish_future_t fut;
    memset(&fut, 0, sizeof(fut));
    fut.done = true;

    publish_future_cancel(&fut.base);
    TEST_ASSERT_TRUE(fut.done);
}

static void test_publish_future_on_ack_unknown_then_duplicate(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    association_t ass[] = { { .remote_id = 10U, .pending_count = 1U }, { .remote_id = 30U, .pending_count = 1U } };

    publish_future_t* const fut =
      (publish_future_t*)mem_alloc_zero(&fixture.cy, sizeof(publish_future_t) + (2U * sizeof(association_t*)));
    TEST_ASSERT_NOT_NULL(fut);

    fut->done            = false;
    fut->acknowledged    = false;
    fut->assoc_capacity  = 2U;
    fut->assoc_remaining = 2U;
    fut->assoc_knockout  = bitmap_new(&fixture.cy, fut->assoc_capacity);
    TEST_ASSERT_NOT_NULL(fut->assoc_knockout);
    fut->assoc_set[0] = &ass[0];
    fut->assoc_set[1] = &ass[1];
    bitmap_set(fut->assoc_knockout, 0U);
    bitmap_set(fut->assoc_knockout, 1U);

    publish_future_on_ack(fut, 20U);
    TEST_ASSERT_TRUE(fut->acknowledged);
    TEST_ASSERT_EQUAL_size_t(2U, fut->assoc_remaining);

    publish_future_on_ack(fut, 10U);
    TEST_ASSERT_EQUAL_size_t(1U, fut->assoc_remaining);

    publish_future_on_ack(fut, 10U);
    TEST_ASSERT_EQUAL_size_t(1U, fut->assoc_remaining);

    mem_free(&fixture.cy, fut->assoc_knockout);
    mem_free(&fixture.cy, fut);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_on_message_ack_stale_seqno_lag_ignored(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t topic;
    memset(&topic, 0, sizeof(topic));
    topic.cy               = &fixture.cy;
    topic.pub_tag_baseline = UINT64_C(1000);
    topic.pub_seqno        = UINT64_C(100005);

    const cy_lane_t lane = { .id = 42U, .p2p = { { 0 } }, .prio = cy_prio_nominal };
    on_message_ack(&fixture.cy, &topic, lane, UINT64_C(1001), 0);

    TEST_ASSERT_EQUAL_size_t(0U, topic.assoc_count);
    TEST_ASSERT_NULL(topic.assoc_by_remote_id);
    TEST_ASSERT_EQUAL_size_t(0U, fixture.async_error_count);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_on_message_ack_allocation_failure_reports_async_error(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t topic;
    memset(&topic, 0, sizeof(topic));
    topic.cy               = &fixture.cy;
    topic.pub_tag_baseline = UINT64_C(500);
    topic.pub_seqno        = UINT64_C(2);

    fixture_set_fail_after(&fixture, 0U);
    const cy_lane_t lane = { .id = 43U, .p2p = { { 0 } }, .prio = cy_prio_nominal };
    on_message_ack(&fixture.cy, &topic, lane, UINT64_C(501), 0);

    TEST_ASSERT_EQUAL_size_t(1U, fixture.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, fixture.last_async_error);
    TEST_ASSERT_EQUAL_size_t(0U, topic.assoc_count);
    TEST_ASSERT_NULL(topic.assoc_by_remote_id);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_on_message_ack_older_than_witness_keeps_witness(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t topic;
    memset(&topic, 0, sizeof(topic));
    topic.cy               = &fixture.cy;
    topic.pub_tag_baseline = UINT64_C(1000);
    topic.pub_seqno        = UINT64_C(3);

    const cy_lane_t lane = { .id = 44U, .p2p = { { 0 } }, .prio = cy_prio_nominal };
    on_message_ack(&fixture.cy, &topic, lane, UINT64_C(1002), 10);
    TEST_ASSERT_EQUAL_size_t(1U, topic.assoc_count);

    association_t* const ass = CAVL2_TO_OWNER(cavl2_min(topic.assoc_by_remote_id), association_t, index_remote_id);
    TEST_ASSERT_NOT_NULL(ass);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(2), ass->seqno_witness);

    on_message_ack(&fixture.cy, &topic, lane, UINT64_C(1001), 11);
    TEST_ASSERT_EQUAL_size_t(1U, topic.assoc_count);
    TEST_ASSERT_EQUAL_UINT64(UINT64_C(2), ass->seqno_witness);
    TEST_ASSERT_EQUAL_size_t(0U, fixture.async_error_count);

    forget_associations(&topic);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_send_message_ack_error_path(void)
{
    fixture_t fixture;
    fixture_init(&fixture);
    fixture.p2p_send_result = CY_ERR_MEDIA;

    const cy_lane_t lane = { .id = 45U, .p2p = { { 0 } }, .prio = cy_prio_nominal };
    send_message_ack(&fixture.cy, lane, UINT64_C(1), UINT64_C(2), 100);

    TEST_ASSERT_EQUAL_size_t(1U, fixture.p2p_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_send_message_ack_success_path(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    const cy_lane_t lane = { .id = 46U, .p2p = { { 0 } }, .prio = cy_prio_nominal };
    send_message_ack(&fixture.cy, lane, UINT64_C(3), UINT64_C(4), 100);

    TEST_ASSERT_EQUAL_size_t(1U, fixture.p2p_send_count);
    TEST_ASSERT_EQUAL_size_t(0U, fixture.async_error_count);
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&fixture.heap));
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_publish_future_is_last_attempt_basic);
    RUN_TEST(test_is_last_attempt_exactly_equal);
    RUN_TEST(test_is_last_attempt_one_over);
    RUN_TEST(test_is_last_attempt_large_margin);
    RUN_TEST(test_is_last_attempt_large_room);
    RUN_TEST(test_is_last_attempt_zero_timeout);
    RUN_TEST(test_is_last_attempt_preserves_full_ack_window);
    RUN_TEST(test_bisect_empty);
    RUN_TEST(test_bisect_single_match);
    RUN_TEST(test_bisect_single_miss_low);
    RUN_TEST(test_bisect_single_miss_high);
    RUN_TEST(test_bisect_multiple_first);
    RUN_TEST(test_bisect_multiple_last);
    RUN_TEST(test_bisect_multiple_middle);
    RUN_TEST(test_bisect_multiple_insert_point);
    RUN_TEST(test_release_no_slack_when_premature);
    RUN_TEST(test_release_slack_incremented_when_conditions_met);
    RUN_TEST(test_release_no_slack_when_seqno_behind_witness);
    RUN_TEST(test_release_no_forget_when_pending_remains);
    RUN_TEST(test_publish_future_cancel_done_is_noop);
    RUN_TEST(test_publish_future_on_ack_unknown_then_duplicate);
    RUN_TEST(test_on_message_ack_stale_seqno_lag_ignored);
    RUN_TEST(test_on_message_ack_allocation_failure_reports_async_error);
    RUN_TEST(test_on_message_ack_older_than_witness_keeps_witness);
    RUN_TEST(test_send_message_ack_error_path);
    RUN_TEST(test_send_message_ack_success_path);
    return UNITY_END();
}
