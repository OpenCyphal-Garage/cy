#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "helpers.h"
#include <string.h>

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    cy_t                 cy;
    guarded_heap_t       heap;
    cy_us_t              now;
    bool                 oom; ///< When true, fixture_realloc returns NULL for new allocations.
} dedup_fixture_t;

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    dedup_fixture_t* const self = (dedup_fixture_t*)platform;
    if (self->oom && (ptr == NULL) && (size > 0)) {
        return NULL;
    }
    return guarded_heap_realloc(&self->heap, ptr, size);
}

static cy_us_t fixture_now(cy_platform_t* const platform) { return ((dedup_fixture_t*)platform)->now; }

static void dedup_fixture_init(dedup_fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0xDED0A110C0FFEE01));
    self->platform.vtable             = &self->vtable;
    self->platform.subject_id_modulus = (uint32_t)CY_SUBJECT_ID_MODULUS_17bit;
    self->platform.cy                 = &self->cy;
    self->vtable.now                  = fixture_now;
    self->vtable.realloc              = fixture_realloc;
    self->cy.platform                 = &self->platform;
}

static void dedup_owner_init(cy_topic_t* const owner, dedup_fixture_t* const fixture)
{
    memset(owner, 0, sizeof(*owner));
    owner->cy                           = &fixture->cy;
    owner->sub_index_dedup_by_remote_id = NULL;
    owner->sub_list_dedup_by_recency    = LIST_EMPTY;
}

static dedup_t* dedup_make_state(cy_topic_t* const owner,
                                 const uint64_t    remote_id,
                                 const uint64_t    tag,
                                 const cy_us_t     now)
{
    dedup_factory_context_t ctx  = { .owner = owner, .remote_id = remote_id, .tag = tag, .now = now };
    cy_tree_t* const        tree = dedup_factory(&ctx);
    TEST_ASSERT_NOT_NULL(tree);
    owner->sub_index_dedup_by_remote_id = tree;
    return CAVL2_TO_OWNER(tree, dedup_t, index_remote_id);
}

static void dedup_cleanup(cy_topic_t* const owner)
{
    dedup_t* const dd = CAVL2_TO_OWNER(owner->sub_index_dedup_by_remote_id, dedup_t, index_remote_id);
    if (dd != NULL) {
        dedup_destroy(dd, owner);
    }
}

static void test_dedup_first_and_exact_duplicate(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_t* const dd = dedup_make_state(&owner, 123U, 100U, 1000);
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 100U, 1000));
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 100U, 1001));

    dedup_cleanup(&owner);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_dedup_out_of_order_seen_once(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_t* const dd = dedup_make_state(&owner, 77U, 200U, 10);
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 200U, 10));
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 199U, 11));
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 199U, 12));

    dedup_cleanup(&owner);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_dedup_wraparound(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_t* const dd = dedup_make_state(&owner, 9U, UINT64_MAX, 0);
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, UINT64_MAX, 0));
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 0U, 1));
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 0U, 2));

    dedup_cleanup(&owner);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

static void test_dedup_drop_stale(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_t* const dd = dedup_make_state(&owner, 0xDEADU, 1234U, 100);
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 1234U, 100));
    dedup_drop_stale(&owner, 100 + SESSION_LIFETIME + 1);
    TEST_ASSERT_NULL(owner.sub_index_dedup_by_remote_id);
    TEST_ASSERT_NULL(owner.sub_list_dedup_by_recency.head);
    TEST_ASSERT_NULL(owner.sub_list_dedup_by_recency.tail);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

/// Forward advance by a small step (1..63): bitmap shifts, previous current-tag bit is set. Covers fwd < DEDUP_HISTORY.
static void test_dedup_forward_small_step(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_t* const dd = dedup_make_state(&owner, 1U, 100U, 0);
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 100U, 0)); // establish tag=100, bitmap=0
    // Advance by 1: fwd=1 < 64, bitmap = (0<<1) | (1<<0) = 1, tag becomes 101.
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 101U, 1));
    // The old tag=100 should be marked as seen (bit 0 of bitmap); re-receiving it is a duplicate.
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 100U, 2));
    // Advance by 2 more: fwd=2, bitmap = (1<<2) | (1<<1) = 6, tag becomes 103.
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 103U, 3));
    // tag=100 is now at rev=3, bit 2 set → duplicate.
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 100U, 4));
    // tag=101 is now at rev=2, bit 1 set → duplicate.
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 101U, 5));
    // tag=99 was never seen → not duplicate (rev=4, bit 3 not set).
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 99U, 6));
    // tag=99 now set in bitmap; re-receiving is duplicate.
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 99U, 7));

    dedup_cleanup(&owner);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

/// Forward advance by exactly DEDUP_HISTORY (64): special case to avoid undefined shift-by-64. Covers
/// fwd==DEDUP_HISTORY.
static void test_dedup_forward_exact_history(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_t* const dd = dedup_make_state(&owner, 2U, 100U, 0);
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 100U, 0)); // establish tag=100, bitmap=0
    // Advance by exactly 64: fwd=64==DEDUP_HISTORY → bitmap = 1<<63, tag becomes 164.
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 164U, 1));
    // The old tag=100 is at rev=64, bit 63 set → duplicate.
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 100U, 2));
    // tag=101 is at rev=63, bit 62 NOT set → not duplicate.
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 101U, 3));

    dedup_cleanup(&owner);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

/// Forward advance by more than DEDUP_HISTORY (>64): bitmap reset (session restart). Covers fwd > DEDUP_HISTORY.
static void test_dedup_forward_large_jump(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_t* const dd = dedup_make_state(&owner, 3U, 100U, 0);
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 100U, 0)); // establish tag=100, bitmap=0
    // Set some bitmap bits first by visiting nearby tags.
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 101U, 1)); // fwd=1 < 64
    // Now jump far ahead: fwd=200 > 64 → bitmap=0, tag becomes 301.
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 301U, 2));
    // Previous tags should NOT be remembered (bitmap was reset).
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 300U, 3)); // rev=1, bit 0 was clear → new
    // But 300 is now set; re-receiving is duplicate.
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 300U, 4));

    dedup_cleanup(&owner);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

/// Factory returns NULL on out-of-memory.
static void test_dedup_factory_oom(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    fixture.oom                 = true;
    dedup_factory_context_t ctx = { .owner = &owner, .remote_id = 42U, .tag = 10U, .now = 0 };
    TEST_ASSERT_NULL(dedup_factory(&ctx));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
}

/// dedup_drop_stale does not remove entries that are still within the session lifetime.
static void test_dedup_drop_stale_not_yet(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_t* const dd = dedup_make_state(&owner, 50U, 500U, 100);
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 500U, 100));
    // Exactly at the boundary: last_active_at(100) + SESSION_LIFETIME >= 100 + SESSION_LIFETIME → not stale.
    dedup_drop_stale(&owner, 100 + SESSION_LIFETIME);
    TEST_ASSERT_NOT_NULL(owner.sub_index_dedup_by_remote_id);
    TEST_ASSERT_EQUAL_size_t(1, guarded_heap_allocated_fragments(&fixture.heap));
    // One tick past → stale.
    dedup_drop_stale(&owner, 100 + SESSION_LIFETIME + 1);
    TEST_ASSERT_NULL(owner.sub_index_dedup_by_remote_id);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

/// dedup_drop_stale removes multiple stale entries, keeping fresh ones.
static void test_dedup_drop_stale_multiple(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    // Create first entry (remote_id=10) at time 100.
    dedup_t* const dd1 = dedup_make_state(&owner, 10U, 1U, 100);
    TEST_ASSERT_FALSE(dedup_update(dd1, &owner, 1U, 100));

    // Create second entry (remote_id=20) at time 200 via cavl2_find_or_insert.
    dedup_factory_context_t ctx2  = { .owner = &owner, .remote_id = 20U, .tag = 2U, .now = 200 };
    cy_tree_t* const        tree2 = cavl2_find_or_insert(
      &owner.sub_index_dedup_by_remote_id, &ctx2.remote_id, dedup_cavl_compare, &ctx2, dedup_factory);
    TEST_ASSERT_NOT_NULL(tree2);
    dedup_t* const dd2 = CAVL2_TO_OWNER(tree2, dedup_t, index_remote_id);
    TEST_ASSERT_FALSE(dedup_update(dd2, &owner, 2U, 200));

    TEST_ASSERT_EQUAL_size_t(2, guarded_heap_allocated_fragments(&fixture.heap));
    // At time 100 + SESSION_LIFETIME + 1, the first entry (last_active=100) is stale; the second (200) is not.
    dedup_drop_stale(&owner, 100 + SESSION_LIFETIME + 1);
    TEST_ASSERT_EQUAL_size_t(1, guarded_heap_allocated_fragments(&fixture.heap));
    // The remaining entry should be the one with remote_id=20.
    dedup_t* const remaining = CAVL2_TO_OWNER(owner.sub_index_dedup_by_remote_id, dedup_t, index_remote_id);
    TEST_ASSERT_NOT_NULL(remaining);
    TEST_ASSERT_EQUAL_UINT64(20U, remaining->remote_id);
    // Now expire the second entry too.
    dedup_drop_stale(&owner, 200 + SESSION_LIFETIME + 1);
    TEST_ASSERT_NULL(owner.sub_index_dedup_by_remote_id);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

/// Exercises all three outcomes of dedup_cavl_compare via the AVL tree with multiple remote IDs.
static void test_dedup_cavl_compare_all_branches(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    // Insert three entries with remote_ids 10, 20, 30 to force compare in all directions.
    dedup_factory_context_t ctx1       = { .owner = &owner, .remote_id = 20U, .tag = 1U, .now = 0 };
    owner.sub_index_dedup_by_remote_id = dedup_factory(&ctx1);
    TEST_ASSERT_NOT_NULL(owner.sub_index_dedup_by_remote_id);
    dedup_t* const dd1 = CAVL2_TO_OWNER(owner.sub_index_dedup_by_remote_id, dedup_t, index_remote_id);
    TEST_ASSERT_FALSE(dedup_update(dd1, &owner, 1U, 0)); // enlist and set last_active_at

    // Insert remote_id=10 (10 < 20, compare returns -1).
    dedup_factory_context_t ctx2 = { .owner = &owner, .remote_id = 10U, .tag = 2U, .now = 0 };
    cy_tree_t* const        t2   = cavl2_find_or_insert(
      &owner.sub_index_dedup_by_remote_id, &ctx2.remote_id, dedup_cavl_compare, &ctx2, dedup_factory);
    TEST_ASSERT_NOT_NULL(t2);
    dedup_t* const dd2 = CAVL2_TO_OWNER(t2, dedup_t, index_remote_id);
    TEST_ASSERT_FALSE(dedup_update(dd2, &owner, 2U, 0));

    // Insert remote_id=30 (30 > 20, compare returns +1).
    dedup_factory_context_t ctx3 = { .owner = &owner, .remote_id = 30U, .tag = 3U, .now = 0 };
    cy_tree_t* const        t3   = cavl2_find_or_insert(
      &owner.sub_index_dedup_by_remote_id, &ctx3.remote_id, dedup_cavl_compare, &ctx3, dedup_factory);
    TEST_ASSERT_NOT_NULL(t3);
    dedup_t* const dd3 = CAVL2_TO_OWNER(t3, dedup_t, index_remote_id);
    TEST_ASSERT_FALSE(dedup_update(dd3, &owner, 3U, 0));

    // Look up existing remote_id=20 (compare returns 0).
    dedup_factory_context_t ctx4  = { .owner = &owner, .remote_id = 20U, .tag = 4U, .now = 0 };
    cy_tree_t* const        found = cavl2_find_or_insert(
      &owner.sub_index_dedup_by_remote_id, &ctx4.remote_id, dedup_cavl_compare, &ctx4, dedup_factory);
    TEST_ASSERT_NOT_NULL(found);
    TEST_ASSERT_EQUAL_UINT64(20U, CAVL2_TO_OWNER(found, dedup_t, index_remote_id)->remote_id);
    TEST_ASSERT_EQUAL_size_t(3, guarded_heap_allocated_fragments(&fixture.heap)); // no extra alloc on lookup

    // Clean up all three.
    dedup_drop_stale(&owner, SESSION_LIFETIME + 1);
    TEST_ASSERT_NULL(owner.sub_index_dedup_by_remote_id);
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_fragments(&fixture.heap));
    TEST_ASSERT_EQUAL_size_t(0, guarded_heap_allocated_bytes(&fixture.heap));
}

/// dedup_drop_stale on an empty list is a no-op (dd==NULL path).
static void test_dedup_drop_stale_empty(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_drop_stale(&owner, 999999);
    TEST_ASSERT_NULL(owner.sub_index_dedup_by_remote_id);
}

void setUp(void) {}

void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_dedup_first_and_exact_duplicate);
    RUN_TEST(test_dedup_out_of_order_seen_once);
    RUN_TEST(test_dedup_wraparound);
    RUN_TEST(test_dedup_drop_stale);
    RUN_TEST(test_dedup_forward_small_step);
    RUN_TEST(test_dedup_forward_exact_history);
    RUN_TEST(test_dedup_forward_large_jump);
    RUN_TEST(test_dedup_factory_oom);
    RUN_TEST(test_dedup_drop_stale_not_yet);
    RUN_TEST(test_dedup_drop_stale_multiple);
    RUN_TEST(test_dedup_drop_stale_empty);
    RUN_TEST(test_dedup_cavl_compare_all_branches);
    return UNITY_END();
}
