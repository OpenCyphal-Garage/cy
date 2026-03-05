#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include "message.h"
#include <string.h>

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    cy_t                 cy;
    guarded_heap_t       heap;
    cy_us_t              now;
    size_t               fail_alloc_size;
    size_t               fail_alloc_count;
    size_t               async_error_count;
    cy_err_t             last_async_error;
    uint16_t             last_async_error_line;
} reorder_fixture_t;

typedef struct
{
    size_t   count;
    uint64_t tags[64];
} arrival_capture_t;

typedef struct
{
    reorder_fixture_t fixture;
    subscriber_root_t root;
    subscriber_t      sub;
    cy_topic_t        topic;
    reordering_t      rr;
    arrival_capture_t capture;
} reorder_env_t;

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    reorder_fixture_t* const self = (reorder_fixture_t*)platform;
    if ((size > 0U) && (self->fail_alloc_count > 0U) && (size == self->fail_alloc_size)) {
        self->fail_alloc_count--;
        return NULL;
    }
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static cy_us_t fixture_now(cy_platform_t* const platform) { return ((reorder_fixture_t*)platform)->now; }

static void fixture_on_async_error(cy_t* const       cy,
                                   cy_topic_t* const topic,
                                   const cy_err_t    error,
                                   const uint16_t    line_number)
{
    (void)topic;
    reorder_fixture_t* const self = (reorder_fixture_t*)cy->platform;
    self->async_error_count++;
    self->last_async_error      = error;
    self->last_async_error_line = line_number;
}

static void on_arrival(cy_future_t* const sub)
{
    const cy_arrival_t arrival = cy_arrival_move(sub);
    if (arrival.message.content == NULL) {
        return;
    }

    arrival_capture_t* const capture = (arrival_capture_t*)cy_future_context(sub).ptr[0];
    TEST_ASSERT_NOT_NULL(capture);
    TEST_ASSERT(capture->count < (sizeof(capture->tags) / sizeof(capture->tags[0])));
    capture->tags[capture->count++] = arrival.breadcrumb.message_tag;
    cy_message_refcount_dec(arrival.message.content);
}

static void assert_message_counters(const size_t destroyed, const size_t live)
{
    TEST_ASSERT_EQUAL_size_t(destroyed, cy_test_message_destroy_count());
    TEST_ASSERT_EQUAL_size_t(live, cy_test_message_live_count());
}

static void reorder_env_init(reorder_env_t* const self)
{
    memset(self, 0, sizeof(*self));

    guarded_heap_init(&self->fixture.heap, UINT64_C(0xA110CA7E5EED1234));
    self->fixture.platform.vtable             = &self->fixture.vtable;
    self->fixture.platform.subject_id_modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    self->fixture.platform.cy                 = &self->fixture.cy;
    self->fixture.vtable.now                  = fixture_now;
    self->fixture.vtable.realloc              = fixture_realloc;
    self->fixture.cy.platform                 = &self->fixture.platform;
    self->fixture.cy.async_error_handler      = fixture_on_async_error;
    self->fixture.now                         = 0;
    self->fixture.fail_alloc_size             = 0;
    self->fixture.fail_alloc_count            = 0;
    self->fixture.async_error_count           = 0;
    self->fixture.last_async_error            = CY_OK;
    self->fixture.last_async_error_line       = 0;
    olga_init(&self->fixture.cy.olga, &self->fixture.cy, olga_now);

    self->root.cy = &self->fixture.cy;

    self->sub.base.index                    = TREE_NULL;
    self->sub.base.key                      = 0;
    self->sub.base.timeout                  = OLGA_EVENT_INIT;
    self->sub.base.cy                       = &self->fixture.cy;
    self->sub.base.context                  = CY_USER_CONTEXT_EMPTY;
    self->sub.base.context.ptr[0]           = &self->capture;
    self->sub.base.callback                 = on_arrival;
    self->sub.base.vtable                   = &subscriber_vtable;
    self->sub.verbatim                      = true;
    self->sub.root                          = &self->root;
    self->sub.next                          = NULL;
    self->sub.message_count                 = 0;
    self->sub.last_arrival                  = (cy_arrival_t){ 0 };
    self->sub.error                         = CY_OK;
    self->sub.disposed                      = false;
    self->sub.params.extent_pure            = 0;
    self->sub.params.reordering_window      = 20;
    self->sub.params.liveness_timeout       = 0;
    self->sub.index_reordering_by_remote_id = NULL;
    self->sub.list_reordering_by_recency    = LIST_EMPTY;

    self->topic.cy   = &self->fixture.cy;
    self->topic.hash = 0xABCDEFULL;

    self->rr.timeout             = OLGA_EVENT_INIT;
    self->rr.remote_id           = 42U;
    self->rr.subscriber          = &self->sub;
    self->rr.topic               = &self->topic;
    self->rr.interned_count      = 0;
    self->rr.interned_by_lin_tag = NULL;
    reordering_resequence(&self->rr, 4U + (uint64_t)(REORDERING_CAPACITY / 2U));
}

static void reorder_env_cleanup(reorder_env_t* const self)
{
    reordering_eject_all(&self->rr);
    olga_cancel(&self->fixture.cy.olga, &self->rr.timeout);
    cy_message_refcount_dec(self->sub.last_arrival.message.content);
    self->sub.last_arrival.message.content = NULL;
}

static bool push_message_rr(reorder_env_t* const self,
                            reordering_t* const  rr,
                            const uint64_t       tag,
                            const cy_us_t        ts,
                            unsigned char        payload);

static bool push_message(reorder_env_t* const self, const uint64_t tag, const cy_us_t ts, const unsigned char payload)
{
    return push_message_rr(self, &self->rr, tag, ts, payload);
}

static bool push_message_rr(reorder_env_t* const self,
                            reordering_t* const  rr,
                            const uint64_t       tag,
                            const cy_us_t        ts,
                            const unsigned char  payload)
{
    cy_message_t* const msg = cy_test_message_make(&self->fixture.heap, &payload, 1);
    TEST_ASSERT_NOT_NULL(msg);
    const cy_message_ts_t mts = { .timestamp = ts, .content = msg };
    const bool            out = reordering_push(rr, tag, cy_prio_nominal, mts);
    cy_message_refcount_dec(msg); // Simulate the caller dropping ownership after reordering_push().
    return out;
}

static reordering_t* make_dynamic_reordering(reorder_env_t* const self,
                                             const uint64_t       remote_id,
                                             const uint64_t       tag,
                                             const cy_us_t        now)
{
    reordering_context_t ctx = {
        .now        = now,
        .lane       = { .id = remote_id, .p2p = { { 0 } }, .prio = cy_prio_nominal },
        .subscriber = &self->sub,
        .topic      = &self->topic,
        .tag        = tag,
    };
    return CAVL2_TO_OWNER(
      cavl2_find_or_insert(
        &self->sub.index_reordering_by_remote_id, &ctx, reordering_cavl_compare, &ctx, reordering_cavl_factory),
      reordering_t,
      index);
}

static void spin_to(reorder_env_t* const self, const cy_us_t now)
{
    self->fixture.now = now;
    (void)olga_spin(&self->fixture.cy.olga);
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

static void test_reordering_refcount_duplicate_and_eject_accounting(void)
{
    reorder_env_t env;
    reorder_env_init(&env);
    assert_message_counters(0U, 0U);

    TEST_ASSERT_TRUE(push_message(&env, 8U, 100, 0x11U)); // interned, retained by reordering state
    TEST_ASSERT_EQUAL_size_t(1U, env.rr.interned_count);
    assert_message_counters(0U, 1U);

    TEST_ASSERT_TRUE(push_message(&env, 8U, 101, 0x22U)); // duplicate tag, dropped idempotently
    TEST_ASSERT_EQUAL_size_t(1U, env.rr.interned_count);
    assert_message_counters(1U, 1U); // duplicate payload must already be destroyed

    spin_to(&env, 1000U); // force ejection of the retained interned message
    TEST_ASSERT_EQUAL_size_t(1U, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_size_t(0U, env.rr.interned_count);
    assert_message_counters(2U, 0U);

    reorder_env_cleanup(&env);
    assert_message_counters(2U, 0U);
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
    TEST_ASSERT_TRUE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));

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
    TEST_ASSERT_TRUE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));

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
    TEST_ASSERT_TRUE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));

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

/// If a newly interned message becomes head-of-line, the timeout must be re-armed to its own window.
static void test_reordering_head_of_line_change_rearms_timeout(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // First out-of-order arrival starts the timer at 100 + 20 = 120.
    TEST_ASSERT_TRUE(push_message(&env, 7U, 100, 0x70U));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);
    TEST_ASSERT_TRUE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));

    // A lower-tag message arrives much later and becomes the new head-of-line.
    // Timeout must move from 120 to 119 + 20 = 139.
    TEST_ASSERT_TRUE(push_message(&env, 6U, 119, 0x60U));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);
    TEST_ASSERT_EQUAL_size_t(2, env.rr.interned_count);
    TEST_ASSERT_TRUE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));

    // Before the re-armed deadline, nothing should be force-ejected.
    spin_to(&env, 120);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);
    TEST_ASSERT_EQUAL_size_t(2, env.rr.interned_count);

    // Gap filler arrives before the new deadline; all should flush in order.
    TEST_ASSERT_TRUE(push_message(&env, 5U, 130, 0x50U));
    TEST_ASSERT_EQUAL_size_t(3, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_UINT64(6U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[2]);
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

/// Regression: a delayed older tag may linearize to a wrapped high value. It must be dropped as late, not treated
/// as a huge forward jump that triggers resequencing.
static void test_reordering_backward_underflow_is_late_drop(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    for (uint64_t tag = 5U; tag <= 15U; tag++) {
        TEST_ASSERT_TRUE(push_message(&env, tag, (cy_us_t)tag, 0xA0U));
    }
    TEST_ASSERT_EQUAL_size_t(11, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(4U, env.rr.tag_baseline);
    TEST_ASSERT_EQUAL_UINT64(11U, env.rr.last_ejected_lin_tag);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    const uint64_t baseline_before = env.rr.tag_baseline;
    const uint64_t last_before     = env.rr.last_ejected_lin_tag;

    TEST_ASSERT_FALSE(push_message(&env, 3U, 200, 0xB0U));
    TEST_ASSERT_EQUAL_size_t(11, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(baseline_before, env.rr.tag_baseline);
    TEST_ASSERT_EQUAL_UINT64(last_before, env.rr.last_ejected_lin_tag);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    TEST_ASSERT_TRUE(push_message(&env, 16U, 201, 0xC0U));
    TEST_ASSERT_EQUAL_size_t(12, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(16U, env.capture.tags[11]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// Capacity overflow triggers resequencing: if a message is too far ahead, all interned messages are ejected
/// and the state is reset. The resequenced message must NOT be ejected immediately because we don't know
/// whether older siblings are about to arrive (see the comment in reordering_resequence).
/// Here we verify the full scenario in capacity-parametric form:
/// baseline 4, establish state via tag=5, then jump to a large tag and backfill all missing older siblings down to
/// the first expected linearized tag. The gap filler must trigger ordered flush of the full backfilled chain.
static void test_reordering_capacity_overflow_resequence(void)
{
    reorder_env_t env;
    reorder_env_init(&env);
    const uint64_t reseq_tag = 50000U;
    const uint64_t half      = (uint64_t)(REORDERING_CAPACITY / 2U);
    TEST_ASSERT_TRUE(half >= 2U);

    // Establish initial state: tag=5 (lin_tag=1) is immediately ejected.
    TEST_ASSERT_TRUE(push_message(&env, 5U, 10, 0x50U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    // Jump far ahead: this triggers resequence and interns the message at lin_tag=capacity/2.
    TEST_ASSERT_TRUE(push_message(&env, reseq_tag, 100, 0xAAU));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count); // Still only the initial tag=5 was delivered.
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);
    TEST_ASSERT_TRUE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));

    // Backfill older siblings from lin_tag=capacity/2-1 down to lin_tag=1.
    // The final push closes the gap and flushes the entire chain in order.
    for (uint64_t offset = 1U; offset < half; offset++) {
        TEST_ASSERT_TRUE(push_message(
          &env, reseq_tag - offset, (cy_us_t)(100U + offset), (unsigned char)(0xA0U + (unsigned char)offset)));
        if (offset < (half - 1U)) {
            TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
            TEST_ASSERT_EQUAL_size_t((size_t)(1U + offset), env.rr.interned_count);
        }
    }

    TEST_ASSERT_EQUAL_size_t((size_t)(1U + half), env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);
    for (uint64_t i = 0U; i < half; i++) {
        TEST_ASSERT_EQUAL_UINT64(reseq_tag - (half - 1U) + i, env.capture.tags[(size_t)(1U + i)]);
    }
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// Capacity overflow may still leave the current message exactly next in order after forced ejection.
/// In that case we should accept it immediately and skip resequencing delay.
static void test_reordering_capacity_overflow_can_fast_path_after_eject_all(void)
{
    reorder_env_t env;
    reorder_env_init(&env);
    const uint64_t capacity = (uint64_t)REORDERING_CAPACITY;

    // Establish baseline progress first: tag=5 => lin_tag=1 ejected.
    TEST_ASSERT_TRUE(push_message(&env, 5U, 10, 0x50U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);

    // Keep a gap at tag=6 and fill interned slots up to the capacity limit.
    for (uint64_t tag = 7U; tag <= (capacity + 5U); tag++) {
        TEST_ASSERT_TRUE(push_message(&env, tag, (cy_us_t)(tag + 4U), (unsigned char)(tag & 0xFFU)));
    }
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_size_t((size_t)(capacity - 1U), env.rr.interned_count);

    // The next tag is just beyond capacity. Forced ejection flushes all interned tags,
    // then the current message becomes exactly next and is ejected immediately.
    TEST_ASSERT_TRUE(push_message(&env, capacity + 6U, (cy_us_t)(capacity + 6U + 4U), 0xE0U));
    TEST_ASSERT_EQUAL_size_t((size_t)(capacity + 1U), env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_UINT64(capacity + 5U, env.capture.tags[(size_t)(capacity - 1U)]);
    TEST_ASSERT_EQUAL_UINT64(capacity + 6U, env.capture.tags[(size_t)capacity]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);
    TEST_ASSERT_FALSE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// Sparse buffered history should be consumed step-by-step on overflow without immediate resequencing.
static void test_reordering_overflow_sparse_stepwise_shift_without_resequence(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    // Establish progress: baseline=4, last_ejected_lin_tag=1 after tag=5.
    TEST_ASSERT_TRUE(push_message(&env, 5U, 10, 0x50U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);
    TEST_ASSERT_EQUAL_UINT64(4U, env.rr.tag_baseline);
    TEST_ASSERT_EQUAL_UINT64(1U, env.rr.last_ejected_lin_tag);

    // Sparse interned set within current window: lin_tags {3,5,9} => tags {7,9,13}.
    TEST_ASSERT_TRUE(push_message(&env, 7U, 11, 0x70U));
    TEST_ASSERT_TRUE(push_message(&env, 9U, 12, 0x90U));
    TEST_ASSERT_TRUE(push_message(&env, 13U, 13, 0xD0U));
    TEST_ASSERT_EQUAL_size_t(3, env.rr.interned_count);
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);

    // Incoming tag=(capacity+10) => lin_tag=(capacity+6) is out of window for last=1.
    // The overflow loop should force-eject sparse buffered tags in multiple iterations:
    // 7, then 9, then 13; this shifts last_ejected to 9, making lin_tag in-window.
    // The current message should then be interned (not resequenced, not immediately ejected).
    TEST_ASSERT_TRUE(push_message(&env, (uint64_t)REORDERING_CAPACITY + 10U, 14, 0x20U));
    TEST_ASSERT_EQUAL_size_t(4, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_UINT64(9U, env.capture.tags[2]);
    TEST_ASSERT_EQUAL_UINT64(13U, env.capture.tags[3]);

    TEST_ASSERT_EQUAL_UINT64(4U, env.rr.tag_baseline); // no resequence
    TEST_ASSERT_EQUAL_UINT64(9U, env.rr.last_ejected_lin_tag);
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);
    TEST_ASSERT_TRUE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// If sparse buffered history is insufficient, stepwise shift should eventually fall back to resequencing.
static void test_reordering_overflow_sparse_stepwise_then_resequence(void)
{
    reorder_env_t env;
    reorder_env_init(&env);
    const uint64_t incoming_tag = (uint64_t)REORDERING_CAPACITY + 24U;
    const uint64_t half         = (uint64_t)(REORDERING_CAPACITY / 2U);
    TEST_ASSERT_TRUE(half >= 2U);

    // Establish progress: baseline=4, last_ejected_lin_tag=1 after tag=5.
    TEST_ASSERT_TRUE(push_message(&env, 5U, 10, 0x50U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);

    // Same sparse buffered set: lin_tags {3,5,9} => tags {7,9,13}.
    TEST_ASSERT_TRUE(push_message(&env, 7U, 11, 0x70U));
    TEST_ASSERT_TRUE(push_message(&env, 9U, 12, 0x90U));
    TEST_ASSERT_TRUE(push_message(&env, 13U, 13, 0xD0U));
    TEST_ASSERT_EQUAL_size_t(3, env.rr.interned_count);

    // Incoming tag=(capacity+24) is too far ahead.
    // Stepwise ejection consumes all sparse buffered slots but still cannot fit lin_tag into the window,
    // so the logic should resequence and intern the current message at lin_tag=capacity/2.
    TEST_ASSERT_TRUE(push_message(&env, incoming_tag, 14, 0x34U));
    TEST_ASSERT_EQUAL_size_t(4, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(7U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_UINT64(9U, env.capture.tags[2]);
    TEST_ASSERT_EQUAL_UINT64(13U, env.capture.tags[3]);

    TEST_ASSERT_EQUAL_UINT64(incoming_tag - half, env.rr.tag_baseline);
    TEST_ASSERT_EQUAL_UINT64(0U, env.rr.last_ejected_lin_tag);
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);
    TEST_ASSERT_TRUE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));

    reordering_slot_t* const slot =
      CAVL2_TO_OWNER(cavl2_min(env.rr.interned_by_lin_tag), reordering_slot_t, index_lin_tag);
    TEST_ASSERT_NOT_NULL(slot);
    TEST_ASSERT_EQUAL_UINT64(half, slot->lin_tag);

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

/// Regression: duplicate of a resequenced message must be caught by interned-slot dedup, not by fast-path ejection.
/// With the fixed constant capacity, resequenced messages land at lin_tag=REORDERING_CAPACITY/2 (>1), so duplicates
/// should miss fast path and be dropped idempotently by the AVL-tree lookup in the interning path.
static void test_reordering_resequence_duplicate_is_deduped(void)
{
    reorder_env_t env;
    reorder_env_init(&env);
    const uint64_t half = (uint64_t)(REORDERING_CAPACITY / 2U);
    TEST_ASSERT_TRUE(half >= 2U);

    // Establish state: tag=5 (lin_tag=1) immediately ejected via fast path.
    TEST_ASSERT_TRUE(push_message(&env, 5U, 10, 0x50U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);

    // Jump far ahead: tag=50000 triggers resequence and is interned at lin_tag=capacity/2.
    TEST_ASSERT_TRUE(push_message(&env, 50000U, 100, 0xAAU));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count); // Only tag=5 delivered so far.
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);

    // Duplicate reliable retransmission should be idempotently dropped by slot dedup.
    TEST_ASSERT_TRUE(push_message(&env, 50000U, 101, 0xFFU));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);     // No new delivery.
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count); // Still just one interned slot, not two.

    // Let the timeout force-eject the single interned message. Verify exactly one delivery of tag=50000.
    spin_to(&env, 1000);
    TEST_ASSERT_EQUAL_size_t(2, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(50000U, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

/// Regression: after resequencing, the oldest admissible older sibling (lin_tag=1) must be accepted, not late-dropped.
/// This validates that the resequence delay still leaves room for older messages to arrive before the frontier.
static void test_reordering_resequence_oldest_older_sibling_accepted(void)
{
    reorder_env_t env;
    reorder_env_init(&env);
    const uint64_t reseq_tag         = 50000U;
    const uint64_t half              = (uint64_t)(REORDERING_CAPACITY / 2U);
    const uint64_t oldest_acceptable = reseq_tag - (half - 1U);
    TEST_ASSERT_TRUE(half >= 2U);

    // Establish state: tag=5 (lin_tag=1) immediately ejected via fast path.
    TEST_ASSERT_TRUE(push_message(&env, 5U, 10, 0x50U));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(5U, env.capture.tags[0]);

    // Jump far ahead: resequenced message is interned waiting for possible older siblings.
    TEST_ASSERT_TRUE(push_message(&env, reseq_tag, 100, 0xAAU));
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);

    // The oldest admissible older sibling should be accepted and ejected immediately.
    TEST_ASSERT_TRUE(push_message(&env, oldest_acceptable, 101, 0xBBU));
    TEST_ASSERT_EQUAL_size_t(2, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(oldest_acceptable, env.capture.tags[1]);
    TEST_ASSERT_EQUAL_size_t(1, env.rr.interned_count);

    // One step older than that must be dropped as late (lin_tag=0).
    TEST_ASSERT_FALSE(push_message(&env, oldest_acceptable - 1U, 102, 0xCCU));
    TEST_ASSERT_EQUAL_size_t(2, env.capture.count);

    // The resequenced message remains interned and will be force-ejected on timeout.
    spin_to(&env, 1000);
    TEST_ASSERT_EQUAL_size_t(3, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(reseq_tag, env.capture.tags[2]);
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

static void test_reordering_push_out_of_memory(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    env.fixture.fail_alloc_size  = sizeof(reordering_slot_t);
    env.fixture.fail_alloc_count = 1;

    // tag=8 with baseline=4 means lin_tag=4 (interning path).
    TEST_ASSERT_FALSE(push_message(&env, 8U, 100, 0x80U));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);
    TEST_ASSERT_EQUAL_size_t(0, env.rr.interned_count);
    TEST_ASSERT_FALSE(olga_is_pending(&env.fixture.cy.olga, &env.rr.timeout));
    TEST_ASSERT_EQUAL_size_t(1, env.fixture.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, env.fixture.last_async_error);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

static void test_reordering_cavl_compare(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    cy_topic_t topic_low  = env.topic;
    cy_topic_t topic_high = env.topic;
    topic_low.hash        = env.topic.hash - 1U;
    topic_high.hash       = env.topic.hash + 1U;

    reordering_t inner;
    memset(&inner, 0, sizeof(inner));
    inner.index                = TREE_NULL;
    inner.list_recency         = LIST_MEMBER_NULL;
    inner.timeout              = OLGA_EVENT_INIT;
    inner.remote_id            = 42U;
    inner.subscriber           = &env.sub;
    inner.topic                = &env.topic;
    inner.tag_baseline         = 0;
    inner.last_ejected_lin_tag = 0;
    inner.interned_count       = 0;
    inner.interned_by_lin_tag  = NULL;

    reordering_context_t ctx = {
        .now        = 0,
        .lane       = { .id = 42U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
        .subscriber = &env.sub,
        .topic      = &env.topic,
        .tag        = 0,
    };

    TEST_ASSERT_EQUAL_INT(0, reordering_cavl_compare(&ctx, &inner.index));

    ctx.topic = &topic_high;
    TEST_ASSERT_EQUAL_INT(+1, reordering_cavl_compare(&ctx, &inner.index));

    ctx.topic = &topic_low;
    TEST_ASSERT_EQUAL_INT(-1, reordering_cavl_compare(&ctx, &inner.index));

    ctx.topic   = &env.topic;
    ctx.lane.id = 43U;
    TEST_ASSERT_EQUAL_INT(+1, reordering_cavl_compare(&ctx, &inner.index));

    ctx.lane.id = 41U;
    TEST_ASSERT_EQUAL_INT(-1, reordering_cavl_compare(&ctx, &inner.index));

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

static void test_reordering_factory_out_of_memory(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    env.fixture.fail_alloc_size  = sizeof(reordering_t);
    env.fixture.fail_alloc_count = 1;

    reordering_context_t ctx = {
        .now        = 0,
        .lane       = { .id = 42U, .p2p = { { 0 } }, .prio = cy_prio_nominal },
        .subscriber = &env.sub,
        .topic      = &env.topic,
        .tag        = 8U,
    };

    const cy_tree_t* const node = cavl2_find_or_insert(
      &env.sub.index_reordering_by_remote_id, &ctx, reordering_cavl_compare, &ctx, reordering_cavl_factory);
    TEST_ASSERT_NULL(node);
    TEST_ASSERT_NULL(env.sub.index_reordering_by_remote_id);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

static void test_reordering_drop_stale_keeps_recent(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    reordering_t* const rr = make_dynamic_reordering(&env, 42U, 8U, 0);
    TEST_ASSERT_NOT_NULL(rr);
    TEST_ASSERT_TRUE(push_message_rr(&env, rr, 8U, 100, 0x80U));
    TEST_ASSERT_EQUAL_size_t(1, rr->interned_count);

    reordering_drop_stale(&env.sub, 100 + SESSION_LIFETIME);
    TEST_ASSERT_NOT_NULL(env.sub.index_reordering_by_remote_id);
    TEST_ASSERT_TRUE(olga_is_pending(&env.fixture.cy.olga, &rr->timeout));
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    reordering_destroy(rr);
    TEST_ASSERT_NULL(env.sub.index_reordering_by_remote_id);
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, env.capture.tags[0]);

    reorder_env_cleanup(&env);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&env.fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&env.fixture.heap));
}

static void test_reordering_drop_stale_removes_old(void)
{
    reorder_env_t env;
    reorder_env_init(&env);

    reordering_t* const rr = make_dynamic_reordering(&env, 42U, 8U, 0);
    TEST_ASSERT_NOT_NULL(rr);
    TEST_ASSERT_TRUE(push_message_rr(&env, rr, 8U, 100, 0x80U));
    TEST_ASSERT_EQUAL_size_t(1, rr->interned_count);
    TEST_ASSERT_EQUAL_size_t(0, env.capture.count);

    reordering_drop_stale(&env.sub, 100 + SESSION_LIFETIME + 1);
    TEST_ASSERT_NULL(env.sub.index_reordering_by_remote_id);
    TEST_ASSERT_EQUAL_size_t(1, env.capture.count);
    TEST_ASSERT_EQUAL_UINT64(8U, env.capture.tags[0]);

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
    RUN_TEST(test_reordering_refcount_duplicate_and_eject_accounting);
    RUN_TEST(test_reordering_gap_closure_flushes_followers);
    RUN_TEST(test_reordering_late_drop);
    RUN_TEST(test_reordering_timeout_forces_ejection);
    RUN_TEST(test_reordering_in_order_1_2_3);
    RUN_TEST(test_reordering_reverse_3_2_1);
    RUN_TEST(test_reordering_first_arrival_delay_for_older);
    RUN_TEST(test_reordering_first_arrival_timeout_without_older);
    RUN_TEST(test_reordering_head_of_line_change_rearms_timeout);
    RUN_TEST(test_reordering_late_after_timeout);
    RUN_TEST(test_reordering_backward_underflow_is_late_drop);
    RUN_TEST(test_reordering_capacity_overflow_resequence);
    RUN_TEST(test_reordering_capacity_overflow_can_fast_path_after_eject_all);
    RUN_TEST(test_reordering_overflow_sparse_stepwise_shift_without_resequence);
    RUN_TEST(test_reordering_overflow_sparse_stepwise_then_resequence);
    RUN_TEST(test_reordering_partial_gap_closure);
    RUN_TEST(test_reordering_resequence_duplicate_is_deduped);
    RUN_TEST(test_reordering_resequence_oldest_older_sibling_accepted);
    RUN_TEST(test_reordering_continuous_in_order_after_gap);
    RUN_TEST(test_reordering_push_out_of_memory);
    RUN_TEST(test_reordering_cavl_compare);
    RUN_TEST(test_reordering_factory_out_of_memory);
    RUN_TEST(test_reordering_drop_stale_keeps_recent);
    RUN_TEST(test_reordering_drop_stale_removes_old);
    return UNITY_END();
}
