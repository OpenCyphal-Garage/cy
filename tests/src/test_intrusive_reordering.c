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
    return UNITY_END();
}
