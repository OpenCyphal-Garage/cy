// Regression tests for C1: an AVL-tree cavl2 factory must not mutate the tree it is being inserted into.
// dedup_factory() and reordering_cavl_factory() used to sweep stale entries out of the very tree that
// cavl2_find_or_insert() was mid-insertion on, freeing the captured parent slot -> heap use-after-free. The fix
// hoists the stale sweep to the on_message() receive path, before the insert. These tests drive the real
// cy_on_message() path so that they exercise the hoisted sweep, and assert structurally (not merely via heap
// accounting, which does NOT discriminate pre/post-fix) that the stale entries were reaped, the new entry was
// created, and the surviving tree is a well-formed single node.
//
// There is no AddressSanitizer in this project. Pre-fix, the corrupt AVL retrace is caught deterministically in debug
// builds by the cavl2 balance-factor assert(); in release builds (asserts off) by a SIGSEGV during the retrace and/or a
// guarded_heap canary/state panic when cy_destroy walks the corrupted tree, plus the always-on Unity structural and
// teardown heap-accounting assertions below. CI runs both, so the regression is caught reliably. Post-fix, the
// structural assertions positively prove the tree is well-formed: stale entries reaped, exactly the new node survives.
// (guarded_heap's quarantine-poison layer re-validates only on eviction past its bound, which never happens in a run
// this small, so it is not the in-run detector for this bug.)

#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include "intrusive_message_fixture.h"

// --------------------------------------------------------------------------------------------------------------------
// C1 (CRITICAL): dedup_factory() must not sweep stale entries out of the dedup tree while cavl2_find_or_insert() is
// mid-insertion on it. Populate several per-remote dedup entries, let them all go stale, then have a reliable message
// from a brand-new remote drive the insert. Pre-fix, the in-factory purge frees the captured parent slot -> UAF.
// --------------------------------------------------------------------------------------------------------------------
static void test_dedup_factory_stale_sweep_during_insert(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("uaf/x"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("uaf/x"));
    TEST_ASSERT_NOT_NULL(topic);

    // Populate the per-remote dedup tree with several entries. Spread the remote-IDs so the tree gains depth and its
    // removal rotates. Do NOT spin (which would let poll() pre-sweep) -- only cy_on_message.
    const uint64_t remotes[] = { 50U, 20U, 80U, 10U, 30U, 70U, 90U, 40U, 60U };
    const size_t   n_remotes = sizeof(remotes) / sizeof(remotes[0]);
    for (size_t i = 0; i < n_remotes; i++) {
        inject_message_from(&fix, topic, remotes[i], true, 1000U + i, (byte_t)(i + 1U));
    }
    for (size_t i = 0; i < n_remotes; i++) { // all entries present before staleness
        TEST_ASSERT_NOT_NULL(find_dedup(topic, remotes[i]));
    }

    // Let every entry become stale (idle > SESSION_LIFETIME).
    fix.now += SESSION_LIFETIME + MEGA;

    // A reliable message from a brand-new remote drives the dedup insert. Pre-fix, dedup_factory -> dedup_drop_stale
    // removes+frees the stale nodes mid-insert, corrupting cavl2_find_or_insert's captured parent slot; post-fix the
    // sweep runs in on_message before the insert, so the insert sees a settled tree.
    const uint64_t new_remote = 999U;
    inject_message_from(&fix, topic, new_remote, true, 5000U, 0xAAU);

    // Structural post-conditions: the stale entries were reaped, exactly the new entry remains, tree well-formed.
    for (size_t i = 0; i < n_remotes; i++) {
        TEST_ASSERT_NULL(find_dedup(topic, remotes[i]));
    }
    cy_tree_t* const root = topic->sub_index_dedup_by_remote_id;
    TEST_ASSERT_NOT_NULL(root);
    TEST_ASSERT_NULL(root->up); // a lone node is the true root: pre-fix out->up is the freed parent, not NULL
    TEST_ASSERT_NULL(root->lr[0]);
    TEST_ASSERT_NULL(root->lr[1]);
    const dedup_t* const nd = CAVL2_TO_OWNER(root, dedup_t, index_remote_id);
    TEST_ASSERT_EQUAL_UINT64(new_remote, nd->remote_id);
    TEST_ASSERT_NOT_NULL(find_dedup(topic, new_remote));

    cy_future_destroy(sub);
    fixture_teardown(&fix);
}

// --------------------------------------------------------------------------------------------------------------------
// C1 (CRITICAL): the reordering variant. An ordered subscriber accumulates per-remote reordering states; they all go
// stale; then a best-effort message from a brand-new remote drives reordering_cavl_factory. Pre-fix, the in-factory
// reordering_drop_stale frees the captured parent slot of sub->index_reordering_by_remote_id -> UAF.
// --------------------------------------------------------------------------------------------------------------------
static void test_reordering_factory_stale_sweep_during_insert(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub_future = cy_subscribe_ordered(fix.cy, cy_str("uaf/r"), 64U, 50 * KILO);
    TEST_ASSERT_NOT_NULL(sub_future);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("uaf/r"));
    TEST_ASSERT_NOT_NULL(topic);
    subscriber_t* const sub = topic_only_subscriber(topic);

    // One reordering state per distinct remote (keyed by remote-ID, topic hash). Spread the IDs for tree depth.
    const uint64_t remotes[] = { 50U, 20U, 80U, 10U, 30U, 70U, 90U, 40U, 60U };
    const size_t   n_remotes = sizeof(remotes) / sizeof(remotes[0]);
    for (size_t i = 0; i < n_remotes; i++) {
        inject_message_from(&fix, topic, remotes[i], false, 1000U + i, (byte_t)(i + 1U));
    }
    for (size_t i = 0; i < n_remotes; i++) { // all >=8 states present -> removal rotates the tree, not a lone root free
        TEST_ASSERT_NOT_NULL(find_reordering_state(sub, topic, remotes[i]));
    }

    // Let every reordering state become stale (no spin -> poll() does not pre-sweep).
    fix.now += SESSION_LIFETIME + MEGA;

    // A message from a brand-new remote drives reordering_cavl_factory -> reordering_drop_stale.
    const uint64_t new_remote = 999U;
    inject_message_from(&fix, topic, new_remote, false, 5000U, 0xAAU);

    // Structural post-conditions: stale states reaped, exactly the new state remains, tree well-formed.
    for (size_t i = 0; i < n_remotes; i++) {
        TEST_ASSERT_NULL(find_reordering_state(sub, topic, remotes[i]));
    }
    cy_tree_t* const root = sub->index_reordering_by_remote_id;
    TEST_ASSERT_NOT_NULL(root);
    TEST_ASSERT_NULL(root->up);
    TEST_ASSERT_NULL(root->lr[0]);
    TEST_ASSERT_NULL(root->lr[1]);
    const reordering_t* const nd = CAVL2_TO_OWNER(root, reordering_t, index);
    TEST_ASSERT_EQUAL_UINT64(new_remote, nd->remote_id);
    TEST_ASSERT_EQUAL_PTR(topic, nd->topic);

    cy_future_destroy(sub_future);
    fixture_teardown(&fix);
}

void setUp(void) {}
void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_dedup_factory_stale_sweep_during_insert);
    RUN_TEST(test_reordering_factory_stale_sweep_during_insert);
    return UNITY_END();
}
