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
#include <unity.h>
#include "guarded_heap.h"
#include "message.h"
#include "intrusive_fixture_utils.h"
#include <string.h>

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    guarded_heap_t       heap;
    cy_t*                cy;
    cy_us_t              now;
    uint64_t             rand_state;

    size_t fail_after;          ///< Fail N-th new allocation when new_alloc_count >= fail_after.
    size_t new_alloc_count;     ///< Counts fresh allocations only.
    size_t pub_send_count;      ///< Counts only user message publications (header types 0 and 1).
    size_t fail_pub_send_after; ///< Message publications fail with CY_ERR_MEDIA once the count exceeds this.

    subject_tracker_t active_readers;
    subject_tracker_t active_writers;
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

static cy_us_t fixture_now(cy_platform_t* const platform) { return ((fixture_t*)platform)->now; }

static uint64_t fixture_random(cy_platform_t* const platform)
{
    return intrusive_random_lcg(&((fixture_t*)platform)->rand_state);
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

static cy_subject_writer_t* fixture_subject_writer_new(cy_platform_t* const platform, const uint32_t subject_id)
{
    fixture_t* const           self = (fixture_t*)platform;
    cy_subject_writer_t* const out  = intrusive_subject_writer_new(&self->heap, subject_id);
    if (out != NULL) {
        subject_tracker_add(&self->active_writers, subject_id);
    }
    return out;
}

static void fixture_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    fixture_t* const self = (fixture_t*)platform;
    subject_tracker_remove(&self->active_writers, writer->subject_id);
    intrusive_subject_writer_destroy(&self->heap, writer);
}

static cy_err_t fixture_subject_writer_send(cy_platform_t* const       platform,
                                            cy_subject_writer_t* const writer,
                                            const cy_us_t              deadline,
                                            const cy_prio_t            priority,
                                            const cy_bytes_t           message)
{
    (void)writer;
    (void)deadline;
    (void)priority;
    fixture_t* const self = (fixture_t*)platform;
    // Locate the first payload byte to discriminate user messages (types 0/1) from gossips/scouts.
    const cy_bytes_t* frag = &message;
    while ((frag != NULL) && ((frag->size == 0U) || (frag->data == NULL))) {
        frag = frag->next;
    }
    const byte_t type = (frag != NULL) ? ((const byte_t*)frag->data)[0] : 0xFFU;
    if ((type == header_msg_be) || (type == header_msg_rel)) {
        self->pub_send_count++;
        if (self->pub_send_count > self->fail_pub_send_after) {
            return CY_ERR_MEDIA;
        }
    }
    return CY_OK;
}

static cy_subject_reader_t* fixture_subject_reader_new(cy_platform_t* const platform,
                                                       const uint32_t       subject_id,
                                                       const size_t         extent)
{
    fixture_t* const           self = (fixture_t*)platform;
    cy_subject_reader_t* const out  = intrusive_subject_reader_new(&self->heap, subject_id, extent);
    if (out != NULL) {
        subject_tracker_add(&self->active_readers, subject_id);
    }
    return out;
}

static void fixture_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    fixture_t* const self = (fixture_t*)platform;
    subject_tracker_remove(&self->active_readers, reader->subject_id);
    intrusive_subject_reader_destroy(&self->heap, reader);
}

static void fixture_subject_reader_extent_set(cy_platform_t* const       platform,
                                              cy_subject_reader_t* const reader,
                                              const size_t               extent)
{
    fixture_t* const self = (fixture_t*)platform;
    subject_tracker_assert_contains(&self->active_readers, reader->subject_id);
    intrusive_subject_reader_extent_set(reader, extent);
}

static cy_err_t fixture_unicast_send(cy_platform_t* const   platform,
                                     const cy_lane_t* const lane,
                                     const cy_us_t          deadline,
                                     const cy_bytes_t       message)
{
    (void)platform;
    (void)lane;
    (void)deadline;
    (void)message;
    return CY_OK; // These tests do not inspect the acknowledgement return path.
}

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->heap, UINT64_C(0x0BADC0DE12345678));
    self->platform.vtable                  = &self->vtable;
    self->platform.subject_id_modulus      = (uint32_t)CY_SUBJECT_ID_MODULUS_16bit;
    self->vtable.subject_writer_new        = fixture_subject_writer_new;
    self->vtable.subject_writer_destroy    = fixture_subject_writer_destroy;
    self->vtable.subject_writer_send       = fixture_subject_writer_send;
    self->vtable.subject_reader_new        = fixture_subject_reader_new;
    self->vtable.subject_reader_destroy    = fixture_subject_reader_destroy;
    self->vtable.subject_reader_extent_set = fixture_subject_reader_extent_set;
    self->vtable.unicast                   = fixture_unicast_send;
    self->vtable.unicast_extent_set        = fixture_unicast_extent_set;
    self->vtable.spin                      = fixture_spin;
    self->vtable.now                       = fixture_now;
    self->vtable.realloc                   = fixture_realloc;
    self->vtable.random                    = fixture_random;
    self->now                              = 1000000;
    self->rand_state                       = UINT64_C(0xFEEDFACECAFEBEEF);
    self->fail_after                       = SIZE_MAX;
    self->fail_pub_send_after              = SIZE_MAX;
    self->cy                               = cy_new(&self->platform, cy_str("home"), cy_str(""), cy_str(""));
    TEST_ASSERT_NOT_NULL(self->cy);
}

static void fixture_advance_to(fixture_t* const self, const cy_us_t now)
{
    TEST_ASSERT_TRUE(now >= self->now);
    self->now = now;
    (void)olga_spin(&self->cy->olga);
}

static void fixture_teardown(fixture_t* const self)
{
    fixture_advance_to(self, self->now + 1); // Let deferred destructions run.
    cy_destroy(self->cy);
    self->cy = NULL;
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self->heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self->heap));
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
}

// Injects a message (best-effort or reliable) into the stack via the unicast path, as if received from a remote.
// Unicast is used because it skips the inline-gossip subject-ID consistency check, simplifying the setup.
static void inject_message_from(fixture_t* const        self,
                                const cy_topic_t* const topic,
                                const uint64_t          remote_id,
                                const bool              reliable,
                                const uint64_t          tag,
                                const byte_t            marker)
{
    byte_t wire[HEADER_BYTES + 4U] = { reliable ? header_msg_rel : header_msg_be, 0, 0, 0xFF /* lage=-1 */ };
    (void)serialize_u32(&wire[4], topic->evictions);
    (void)serialize_u64(&wire[8], topic->hash);
    (void)serialize_u64(&wire[16], tag);
    wire[HEADER_BYTES + 0U] = marker;
    wire[HEADER_BYTES + 1U] = (byte_t)(marker + 1U);
    wire[HEADER_BYTES + 2U] = (byte_t)(marker + 2U);
    wire[HEADER_BYTES + 3U] = (byte_t)(marker + 3U);
    cy_message_t* const msg = cy_test_message_make(&self->heap, wire, sizeof(wire));
    TEST_ASSERT_NOT_NULL(msg);
    cy_lane_t lane            = { 0 };
    lane.id                   = remote_id;
    lane.prio                 = cy_prio_nominal;
    const cy_message_ts_t mts = { .timestamp = self->now, .content = msg };
    cy_on_message(&self->platform, lane, NULL, mts);
}

// Finds a reordering state by (remote-ID, topic) in the subscriber's index, or NULL if absent.
static cy_tree_t* find_reordering_state(subscriber_t* const sub, cy_topic_t* const topic, const uint64_t remote_id)
{
    reordering_context_t key = { 0 };
    key.lane.id              = remote_id;
    key.topic                = topic;
    return cavl2_find(sub->index_reordering_by_remote_id, &key, reordering_cavl_compare);
}

// --------------------------------------------------------------------------------------------------------------------
// C1 (CRITICAL): dedup_factory() must not sweep stale entries out of the dedup tree while cavl2_find_or_insert() is
// mid-insertion on it. Populate several per-remote dedup entries, let them all go stale, then have a reliable message
// from a brand-new remote drive the insert. Pre-fix, the in-factory purge frees the captured parent slot -> UAF.
// --------------------------------------------------------------------------------------------------------------------
static void test_dedup_factory_stale_sweep_during_insert(void)
{
    fixture_t fix;
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
        TEST_ASSERT_NOT_NULL(cavl2_find(topic->sub_index_dedup_by_remote_id, &remotes[i], dedup_cavl_compare));
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
        TEST_ASSERT_NULL(cavl2_find(topic->sub_index_dedup_by_remote_id, &remotes[i], dedup_cavl_compare));
    }
    cy_tree_t* const root = topic->sub_index_dedup_by_remote_id;
    TEST_ASSERT_NOT_NULL(root);
    TEST_ASSERT_NULL(root->up); // a lone node is the true root: pre-fix out->up is the freed parent, not NULL
    TEST_ASSERT_NULL(root->lr[0]);
    TEST_ASSERT_NULL(root->lr[1]);
    const dedup_t* const nd = CAVL2_TO_OWNER(root, dedup_t, index_remote_id);
    TEST_ASSERT_EQUAL_UINT64(new_remote, nd->remote_id);
    TEST_ASSERT_NOT_NULL(cavl2_find(topic->sub_index_dedup_by_remote_id, &new_remote, dedup_cavl_compare));

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
    fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub_future = cy_subscribe_ordered(fix.cy, cy_str("uaf/r"), 64U, 50 * KILO);
    TEST_ASSERT_NOT_NULL(sub_future);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("uaf/r"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_NOT_NULL(topic->couplings);
    subscriber_t* const sub = topic->couplings->root->head;
    TEST_ASSERT_NOT_NULL(sub);

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
