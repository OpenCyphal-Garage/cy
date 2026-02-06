#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include <stdlib.h>
#include <string.h>

typedef struct
{
    cy_t        cy;
    cy_vtable_t vtable;
    cy_us_t     now;
} dedup_fixture_t;

static void* fixture_realloc(cy_t* const cy, void* const ptr, const size_t size)
{
    (void)cy;
    if (size == 0U) {
        free(ptr);
        return NULL;
    }
    return realloc(ptr, size);
}

static cy_us_t fixture_now(const cy_t* const cy) { return ((const dedup_fixture_t*)cy)->now; }

static void dedup_fixture_init(dedup_fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    self->vtable.now     = fixture_now;
    self->vtable.realloc = fixture_realloc;
    self->cy.vtable      = &self->vtable;
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
}

static void test_dedup_wraparound(void)
{
    dedup_fixture_t fixture;
    cy_topic_t      owner;
    dedup_fixture_init(&fixture);
    dedup_owner_init(&owner, &fixture);

    dedup_t* const dd = dedup_make_state(&owner, 9U, TAG56_MASK, 0);
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, TAG56_MASK, 0));
    TEST_ASSERT_FALSE(dedup_update(dd, &owner, 0U, 1));
    TEST_ASSERT_TRUE(dedup_update(dd, &owner, 0U, 2));

    dedup_cleanup(&owner);
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
    return UNITY_END();
}
