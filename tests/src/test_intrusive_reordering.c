#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "helpers.h"
#include "message.h"
#include <string.h>

typedef struct
{
    cy_t           cy;
    cy_vtable_t    vtable;
    guarded_heap_t heap;
    olga_t         olga;
    cy_us_t        now;
} reorder_fixture_t;

typedef struct
{
    size_t   count;
    uint64_t tags[16];
} arrival_capture_t;

typedef struct
{
    reorder_fixture_t fixture;
    subscriber_root_t root;
    cy_subscriber_t   sub;
    cy_topic_t        topic;
    reordering_t      rr;
    arrival_capture_t capture;
} reorder_env_t;

static void* fixture_realloc(cy_t* const cy, void* const ptr, const size_t size)
{
    reorder_fixture_t* const self = (reorder_fixture_t*)cy;
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static cy_us_t fixture_now(const cy_t* const cy) { return ((const reorder_fixture_t*)cy)->now; }

static void on_arrival(cy_subscriber_t* const sub, const cy_arrival_t arrival)
{
    arrival_capture_t* const capture = (arrival_capture_t*)sub->user_context.ptr[0];
    TEST_ASSERT_NOT_NULL(capture);
    TEST_ASSERT(capture->count < (sizeof(capture->tags) / sizeof(capture->tags[0])));
    capture->tags[capture->count++] = arrival.breadcrumb.message_tag;
}

static void reorder_env_init(reorder_env_t* const self)
{
    memset(self, 0, sizeof(*self));

    guarded_heap_init(&self->fixture.heap, UINT64_C(0xA110CA7E5EED1234));
    self->fixture.vtable.now     = fixture_now;
    self->fixture.vtable.realloc = fixture_realloc;
    self->fixture.cy.vtable      = &self->fixture.vtable;
    self->fixture.cy.olga        = &self->fixture.olga;
    self->fixture.now            = 0;
    olga_init(&self->fixture.olga, &self->fixture.cy, olga_now);

    self->root.cy = &self->fixture.cy;

    self->sub.root                          = &self->root;
    self->sub.params.extent                 = 0;
    self->sub.params.reordering_window      = 20;
    self->sub.params.reordering_capacity    = 8;
    self->sub.index_reordering_by_remote_id = NULL;
    self->sub.list_reordering_by_recency    = LIST_EMPTY;
    self->sub.callback                      = on_arrival;
    self->sub.user_context                  = CY_USER_CONTEXT_EMPTY;
    self->sub.user_context.ptr[0]           = &self->capture;

    self->topic.cy   = &self->fixture.cy;
    self->topic.hash = 0xABCDEFULL;

    self->rr.timeout                     = OLGA_EVENT_INIT;
    self->rr.remote_id                   = 42U;
    self->rr.subscriber                  = &self->sub;
    self->rr.topic                       = &self->topic;
    self->rr.substitutions.count         = 0;
    self->rr.substitutions.substitutions = NULL;
    self->rr.interned_count              = 0;
    self->rr.interned_by_lin_tag         = NULL;
    reordering_resequence(&self->rr, 8U);
}

static void reorder_env_cleanup(reorder_env_t* const self)
{
    reordering_eject_all(&self->rr);
    olga_cancel(self->fixture.cy.olga, &self->rr.timeout);
}

static bool push_message(reorder_env_t* const self, const uint64_t tag, const cy_us_t ts, const unsigned char payload)
{
    cy_message_t* const msg = cy_test_message_make(&self->fixture.heap, &payload, 1);
    TEST_ASSERT_NOT_NULL(msg);
    const cy_message_ts_t mts = { .timestamp = ts, .content = msg };
    const bool            out = reordering_push(&self->rr, tag, mts);
    cy_message_refcount_dec(msg); // Simulate the caller dropping ownership after reordering_push().
    return out;
}

static void spin_to(reorder_env_t* const self, const cy_us_t now)
{
    self->fixture.now = now;
    (void)olga_spin(self->fixture.cy.olga);
}

static void test_reordering_duplicate_interned_message_is_idempotent(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    TEST_ASSERT_TRUE(push_message(&env, 8U, 100, 0x11U));
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    TEST_ASSERT_TRUE(push_message(&env, 8U, 101, 0x22U));
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    spin_to(&env, 1000);
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

static void test_reordering_gap_closure_flushes_followers(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    TEST_ASSERT_TRUE(push_message(&env, 7U, 10, 0x10U));
    TEST_ASSERT_TRUE(push_message(&env, 8U, 11, 0x20U));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    TEST_ASSERT_TRUE(push_message(&env, 5U, 12, 0x30U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);

    TEST_ASSERT_TRUE(push_message(&env, 6U, 13, 0x40U));
    TEST_ASSERT_EQUAL_size_t(4, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_UINT64(6U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[2]);
    TEST_ASSERT_EQUAL_UINT64(8U, env.capture.tags[3]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

static void test_reordering_late_drop(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    TEST_ASSERT_TRUE(push_message(&env, 5U, 10, 0x11U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);

    TEST_ASSERT_FALSE(push_message(&env, 5U, 11, 0x22U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

static void test_reordering_timeout_forces_ejection(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    TEST_ASSERT_TRUE(push_message(&env, 8U, 100, 0x01U));
    TEST_ASSERT_TRUE(push_message(&env, 9U, 101, 0x02U));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);
    TEST_ASSERT_TRUE(olga_is_pending(env.fixture.cy.olga, &env.rr.timeout));

    spin_to(&env, 1000);
    TEST_ASSERT_EQUAL_size_t(2, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_UINT64(9U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// Sequential in-order arrival (tags 5, 6, 7 with baseline 4): immediate ejection path, no interning needed.
static void test_reordering_in_order_1_2_3(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // tag=5, lin_tag=1 => matches last_ejected_lin_tag+1 => immediate eject
    TEST_ASSERT_TRUE(push_message(&env, 5U, 10, 0xAAU));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    // tag=6, lin_tag=2 => immediate eject
    TEST_ASSERT_TRUE(push_message(&env, 6U, 11, 0xBBU));
    TEST_ASSERT_EQUAL_size_t(2, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(6U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    // tag=7, lin_tag=3 => immediate eject
    TEST_ASSERT_TRUE(push_message(&env, 7U, 12, 0xCCU));
    TEST_ASSERT_EQUAL_size_t(3, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[2]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// Reverse arrival (tags 7, 6, 5 with baseline 4): messages 7 and 6 are interned awaiting the gap filler 5.
/// When 5 arrives it triggers immediate ejection of the chain 5->6->7.
static void test_reordering_reverse_3_2_1(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // tag=7, lin_tag=3 => gap (expected lin=1), interned
    TEST_ASSERT_TRUE(push_message(&env, 7U, 10, 0xCCU));
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);
    TEST_ASSERT_TRUE(olga_is_pending(env.fixture.cy.olga, &env.rr.timeout));

    // tag=6, lin_tag=2 => gap (expected lin=1), interned
    TEST_ASSERT_TRUE(push_message(&env, 6U, 11, 0xBBU));
    TEST_ASSERT_EQUAL_size_t(2, env.rr.interned_count);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    // tag=5, lin_tag=1 => matches expected, ejects 5, then scan flushes 6 and 7
    TEST_ASSERT_TRUE(push_message(&env, 5U, 12, 0xAAU));
    TEST_ASSERT_EQUAL_size_t(3, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_UINT64(6U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[2]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// First message may have older siblings: we delay delivery to give them time to arrive.
/// If an older message arrives within the window, it should be delivered first.
static void test_reordering_first_arrival_delay_for_older(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // First arrival is tag=7 (lin_tag=3). The reordering state cannot deliver it immediately because
    // it doesn't know if tags 5 or 6 might follow shortly (they could be coming from a slower link).
    TEST_ASSERT_TRUE(push_message(&env, 7U, 100, 0x70U));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);
    TEST_ASSERT_TRUE(olga_is_pending(env.fixture.cy.olga, &env.rr.timeout));

    // Shortly after, the "older" message tag=6 arrives (lin_tag=2). Still waiting for tag=5.
    TEST_ASSERT_TRUE(push_message(&env, 6U, 102, 0x60U));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);
    TEST_ASSERT_EQUAL_size_t(2, env.rr.interned_count);

    // Now tag=5 (lin_tag=1) arrives within the window. All three should flush in order.
    TEST_ASSERT_TRUE(push_message(&env, 5U, 105, 0x50U));
    TEST_ASSERT_EQUAL_size_t(3, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_UINT64(6U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[2]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// When the first message arrives with a gap ahead and the older messages never come,
/// the reordering window timeout should force ejection.
static void test_reordering_first_arrival_timeout_without_older(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // Receive tag=7 first (lin_tag=3), but tags 5 and 6 never arrive.
    TEST_ASSERT_TRUE(push_message(&env, 7U, 100, 0x70U));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);

    // Before the window expires, no delivery.
    spin_to(&env, 110);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    // After the window expires (timestamp 100 + reordering_window 20 = 120), force eject.
    spin_to(&env, 121);
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// After the window expires and force-ejects, a late older message should be dropped.
static void test_reordering_late_after_timeout(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // Receive tag=7 first, wait for timeout.
    TEST_ASSERT_TRUE(push_message(&env, 7U, 100, 0x70U));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    spin_to(&env, 121);
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[0]);

    // The late tag=5 should be rejected (lin_tag=1, but last_ejected is now 3).
    TEST_ASSERT_FALSE(push_message(&env, 5U, 200, 0x50U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);

    // The late tag=6 should also be rejected.
    TEST_ASSERT_FALSE(push_message(&env, 6U, 201, 0x60U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);

    // The next in-order tag=8 (lin_tag=4) should be accepted.
    TEST_ASSERT_TRUE(push_message(&env, 8U, 202, 0x80U));
    TEST_ASSERT_EQUAL_size_t(2, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, env.capture.tags[1]);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// Capacity overflow triggers resequencing: if a message is too far ahead, all interned messages are ejected
/// and the state is reset.
static void test_reordering_capacity_overflow_resequence(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // Intern tag=6 (lin_tag=2), normal gap.
    TEST_ASSERT_TRUE(push_message(&env, 6U, 10, 0x60U));
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    // Push a tag that is much further ahead than the capacity (8) allows.
    // With last_ejected_lin_tag=0 and capacity=8, any lin_tag > 8 triggers resequence.
    // tag_baseline=4, so we need tag such that tag56_forward_distance(4, tag) > 8 + 0 = 8.
    // tag = 4 + 9 = 13 => lin_tag = 9 > 8 => resequence!
    TEST_ASSERT_TRUE(push_message(&env, 13U, 11, 0xD0U));
    // The old interned message (tag=6) should have been force-ejected before the resequence.
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(6U, env.capture.tags[0]);
    // After resequence, the new message (tag=13) is interned awaiting ordering context.
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);

    // Let the new resequenced state timeout.
    spin_to(&env, 1000);
    TEST_ASSERT_EQUAL_size_t(2, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(13U, env.capture.tags[1]);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// Partial gap closure: middle message arrives closing a partial chain but leaving remaining gaps.
static void test_reordering_partial_gap_closure(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // Intern tags 7 and 8 (lin_tags 3 and 4). Tags 5 and 6 (lin_tags 1, 2) are missing.
    TEST_ASSERT_TRUE(push_message(&env, 7U, 10, 0x70U));
    TEST_ASSERT_TRUE(push_message(&env, 8U, 11, 0x80U));
    TEST_ASSERT_EQUAL_size_t(2, env.rr.interned_count);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    // Now tag=5 (lin_tag=1) arrives. It ejects 5 immediately but 6 is still missing, so 7 and 8 stay interned.
    TEST_ASSERT_TRUE(push_message(&env, 5U, 12, 0x50U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);
    // 7 and 8 are still interned (gap at lin_tag=2 which is tag=6).
    TEST_ASSERT_EQUAL_size_t(2, env.rr.interned_count);

    // Now tag=6 (lin_tag=2) arrives, closing the gap. Chain 6->7->8 flushes.
    TEST_ASSERT_TRUE(push_message(&env, 6U, 13, 0x60U));
    TEST_ASSERT_EQUAL_size_t(4, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(6U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[2]);
    TEST_ASSERT_EQUAL_UINT64(8U, env.capture.tags[3]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// After full in-order delivery, verify that subsequent in-order messages continue to be ejected immediately.
static void test_reordering_continuous_in_order_after_gap(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // Reverse order first: 7, 6, 5
    TEST_ASSERT_TRUE(push_message(&env, 7U, 10, 0x70U));
    TEST_ASSERT_TRUE(push_message(&env, 6U, 11, 0x60U));
    TEST_ASSERT_TRUE(push_message(&env, 5U, 12, 0x50U));
    TEST_ASSERT_EQUAL_size_t(3, env.capture.count);

    // Now continue in order: 8, 9, 10
    TEST_ASSERT_TRUE(push_message(&env, 8U, 13, 0x80U));
    TEST_ASSERT_EQUAL_size_t(4, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, env.capture.tags[3]);

    TEST_ASSERT_TRUE(push_message(&env, 9U, 14, 0x90U));
    TEST_ASSERT_EQUAL_size_t(5, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(9U, env.capture.tags[4]);

    TEST_ASSERT_TRUE(push_message(&env, 10U, 15, 0xA0U));
    TEST_ASSERT_EQUAL_size_t(6, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(10U, env.capture.tags[5]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

void setUp(void)
{
    TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count());
    cy_test_message_reset_counters();
}

void tearDown(void) { TEST_ASSERT_EQUAL_size_t(0, cy_test_message_live_count()); }

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_reordering_duplicate_interned_message_is_idempotent);
    RUN_TEST(test_reordering_gap_closure_flushes_followers);
    RUN_TEST(test_reordering_late_drop);
    RUN_TEST(test_reordering_timeout_forces_ejection);
    RUN_TEST(test_reordering_in_order_1_2_3);
    RUN_TEST(test_reordering_reverse_3_2_1);
    RUN_TEST(test_reordering_first_arrival_delay_for_older);
    RUN_TEST(test_reordering_first_arrival_timeout_without_older);
    RUN_TEST(test_reordering_late_after_timeout);
    RUN_TEST(test_reordering_capacity_overflow_resequence);
    RUN_TEST(test_reordering_partial_gap_closure);
    RUN_TEST(test_reordering_continuous_in_order_after_gap);
    return UNITY_END();
}
