// Regression tests for H2: topics created locally (cy_advertise / verbatim cy_subscribe) after a matching pattern
// subscription must couple to the pre-existing pattern roots, exactly like topics learned from gossip do.
// Also verifies the keep-topic-on-coupling-OOM policy specific to the local creation path.

#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include "intrusive_message_fixture.h"

static size_t count_couplings(const cy_topic_t* const topic)
{
    size_t count = 0U;
    for (const cy_topic_coupling_t* cpl = topic->couplings; cpl != NULL; cpl = cpl->next) {
        count++;
    }
    return count;
}

typedef struct
{
    size_t count;
} async_error_sink_t;

static void on_diag_async_error(cy_diag_t* const  diag,
                                cy_topic_t* const topic,
                                const cy_err_t    error,
                                const uint16_t    line_number)
{
    (void)topic;
    (void)error;
    (void)line_number;
    ((async_error_sink_t*)diag->user_context.ptr[0])->count++;
}

static const cy_diag_vtable_t async_error_counter_vtable = {
    .async_error = on_diag_async_error,
};

// Pattern subs first, then a local advertisement: all matching roots couple, the reader exists for remote traffic,
// and every injected message is delivered to every pattern subscriber exactly once.
static void test_pattern_then_advertise_couples_multi_root(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const pat_one = cy_subscribe(fix.cy, cy_str("x/*"), 512U);
    cy_future_t* const pat_any = cy_subscribe(fix.cy, cy_str("x/>"), 128U);
    TEST_ASSERT_NOT_NULL(pat_one);
    TEST_ASSERT_NOT_NULL(pat_any);

    cy_publisher_t* const pub = cy_advertise(fix.cy, cy_str("x/b"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("x/b"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_EQUAL_size_t(2U, count_couplings(topic));
    TEST_ASSERT_NOT_NULL(topic->sub_reader);
    TEST_ASSERT_EQUAL_UINT32(topic_subject_id(topic), topic->sub_reader->handle->subject_id);
    TEST_ASSERT_EQUAL_size_t(512U + HEADER_BYTES, topic->sub_reader->handle->extent);

    inject_message(&fix, topic, false, 100U, 11U);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat_one));
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat_any));
    inject_message(&fix, topic, false, 101U, 22U);
    TEST_ASSERT_EQUAL_UINT64(2U, cy_arrival_count(pat_one));
    TEST_ASSERT_EQUAL_UINT64(2U, cy_arrival_count(pat_any));

    cy_unadvertise(pub);
    cy_future_destroy(pat_one);
    cy_future_destroy(pat_any);
    fixture_teardown(&fix);
}

// Flip of the H2 reference case: pattern first, verbatim subscription second. Both couple; a later pattern root
// still couples too; deliveries are exactly-once per subscriber per message.
static void test_pattern_then_verbatim_subscribe_couples(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const pat = cy_subscribe(fix.cy, cy_str("order/*"), 512U);
    TEST_ASSERT_NOT_NULL(pat);
    cy_future_t* const verb = cy_subscribe(fix.cy, cy_str("order/a"), 16U);
    TEST_ASSERT_NOT_NULL(verb);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("order/a"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_EQUAL_size_t(2U, count_couplings(topic));

    inject_message(&fix, topic, false, 100U, 33U);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(verb));
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat));

    cy_future_t* const pat2 = cy_subscribe(fix.cy, cy_str("order/>"), 512U);
    TEST_ASSERT_NOT_NULL(pat2);
    TEST_ASSERT_EQUAL_size_t(3U, count_couplings(topic));
    inject_message(&fix, topic, false, 101U, 44U);
    TEST_ASSERT_EQUAL_UINT64(2U, cy_arrival_count(verb));
    TEST_ASSERT_EQUAL_UINT64(2U, cy_arrival_count(pat));
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat2));

    cy_future_destroy(pat);
    cy_future_destroy(pat2);
    cy_future_destroy(verb);
    fixture_teardown(&fix);
}

// Control: the previously-working order (topic first, pattern second) must not double-couple, and repeated
// advertisement of the same name must not add couplings.
static void test_advertise_then_pattern_no_double_coupling(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_publisher_t* const pub = cy_advertise(fix.cy, cy_str("y/a"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_future_t* const pat = cy_subscribe(fix.cy, cy_str("y/*"), 64U);
    TEST_ASSERT_NOT_NULL(pat);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("y/a"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_EQUAL_size_t(1U, count_couplings(topic));

    cy_publisher_t* const pub2 = cy_advertise(fix.cy, cy_str("y/a"));
    TEST_ASSERT_NOT_NULL(pub2);
    TEST_ASSERT_EQUAL_size_t(1U, count_couplings(topic));

    inject_message(&fix, topic, false, 100U, 55U);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat));

    cy_unadvertise(pub);
    cy_unadvertise(pub2);
    cy_future_destroy(pat);
    fixture_teardown(&fix);
}

// Substitutions recorded for a coupling created by local advertisement must match the gossip-path behavior and
// point into the topic-owned name storage (NOT into the transient resolution buffer of the advertise call).
static void test_substitutions_on_local_topic(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const pat = cy_subscribe(fix.cy, cy_str("s/*/y/>"), 64U);
    TEST_ASSERT_NOT_NULL(pat);
    cy_publisher_t* const pub = cy_advertise(fix.cy, cy_str("s/foo/y/a/b"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("s/foo/y/a/b"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_EQUAL_size_t(1U, count_couplings(topic));

    const cy_substitution_set_t subs = cy_subscriber_substitutions(pat, topic);
    TEST_ASSERT_EQUAL_size_t(3U, subs.count);
    TEST_ASSERT_NOT_NULL(subs.substitutions);
    TEST_ASSERT_EQUAL_size_t(0U, subs.substitutions[0].ordinal);
    TEST_ASSERT_EQUAL_size_t(1U, subs.substitutions[1].ordinal);
    TEST_ASSERT_EQUAL_size_t(1U, subs.substitutions[2].ordinal);
    TEST_ASSERT_EQUAL_MEMORY("foo", subs.substitutions[0].str.str, 3U);
    TEST_ASSERT_EQUAL_MEMORY("a", subs.substitutions[1].str.str, 1U);
    TEST_ASSERT_EQUAL_MEMORY("b", subs.substitutions[2].str.str, 1U);
    const cy_str_t name = cy_topic_name(topic);
    for (size_t i = 0U; i < subs.count; i++) {
        const cy_substitution_t s   = subs.substitutions[i];
        const uintptr_t         beg = (uintptr_t)s.str.str;
        const uintptr_t         end = beg + s.str.len;
        TEST_ASSERT_TRUE((beg >= (uintptr_t)name.str) && (end <= ((uintptr_t)name.str + name.len)));
    }

    cy_unadvertise(pub);
    cy_future_destroy(pat);
    fixture_teardown(&fix);
}

// A pinned local advertisement couples to pre-existing patterns just like an unpinned one; the reader is acquired
// on the pinned subject-ID.
static void test_pinned_local_advertise_couples(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const pat = cy_subscribe(fix.cy, cy_str("p/*"), 64U);
    TEST_ASSERT_NOT_NULL(pat);
    cy_publisher_t* const pub = cy_advertise(fix.cy, cy_str("p/x#7"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("p/x"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_EQUAL_UINT32(UINT32_MAX - 7U, topic->evictions);
    TEST_ASSERT_EQUAL_size_t(1U, count_couplings(topic));
    TEST_ASSERT_NOT_NULL(topic->sub_reader);
    TEST_ASSERT_EQUAL_UINT32(7U, topic->sub_reader->handle->subject_id);

    inject_message(&fix, topic, false, 100U, 66U);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat));

    cy_unadvertise(pub);
    cy_future_destroy(pat);
    fixture_teardown(&fix);
}

// Sweep every allocation failure point across cy_advertise with a pre-existing pattern subscription:
// - advertise either fails cleanly (no topic left behind) or succeeds with the topic alive;
// - a coupling OOM keeps the topic and reports an async error instead of destroying it;
// - re-subscribing the pattern repairs the missing coupling (the only self-heal path);
// - no leaks in any iteration.
static void test_coupling_oom_keeps_topic(void)
{
    bool saw_coupling_oom = false;
    bool saw_clean_run    = false;
    for (size_t n = 0U; (n < 64U) && !saw_clean_run; n++) {
        msg_fixture_t fix;
        fixture_init(&fix);
        async_error_sink_t sink = { 0U };
        cy_diag_t diag = { .next = NULL, .user_context = CY_USER_CONTEXT_EMPTY, .vtable = &async_error_counter_vtable };
        diag.user_context.ptr[0] = &sink;
        cy_diag_add(fix.cy, &diag);

        cy_future_t* const pat = cy_subscribe(fix.cy, cy_str("oom/*"), 64U);
        TEST_ASSERT_NOT_NULL(pat);

        fix.new_alloc_count       = 0U;
        fix.fail_after            = n;
        cy_publisher_t* const pub = cy_advertise(fix.cy, cy_str("oom/t"));
        fix.fail_after            = SIZE_MAX;

        cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("oom/t"));
        if (pub == NULL) {
            TEST_ASSERT_NULL(topic); // Clean rollback: a failed advertise leaves no topic behind.
        } else {
            TEST_ASSERT_NOT_NULL(topic); // Coupling/reader OOM must NOT destroy a locally requested topic.
            if (count_couplings(topic) == 0U) {
                TEST_ASSERT_TRUE(sink.count > 0U);
                saw_coupling_oom = true;
                // Re-subscribing the same pattern couples the topic that was orphaned by the OOM.
                cy_future_t* const pat2 = cy_subscribe(fix.cy, cy_str("oom/*"), 64U);
                TEST_ASSERT_NOT_NULL(pat2);
                TEST_ASSERT_EQUAL_size_t(1U, count_couplings(topic));
                inject_message(&fix, topic, false, 100U, 77U);
                TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat2));
                cy_future_destroy(pat2);
            } else {
                TEST_ASSERT_EQUAL_size_t(1U, count_couplings(topic));
                saw_clean_run = sink.count == 0U;
            }
            cy_unadvertise(pub);
        }
        cy_future_destroy(pat);
        fixture_teardown(&fix);
    }
    TEST_ASSERT_TRUE(saw_coupling_oom);
    TEST_ASSERT_TRUE(saw_clean_run);
}

// Lifecycle: destroying the pattern subscriber decouples and releases the reader while the publisher lives on;
// once the publisher is also gone, the pattern-only topic demotes to implicit and is retired on timeout.
static void test_lifecycle_decouple_and_retire(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const pat = cy_subscribe(fix.cy, cy_str("l/*"), 64U);
    TEST_ASSERT_NOT_NULL(pat);
    cy_publisher_t* const pub = cy_advertise(fix.cy, cy_str("l/a"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("l/a"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_EQUAL_size_t(1U, count_couplings(topic));
    TEST_ASSERT_NOT_NULL(topic->sub_reader);

    cy_future_destroy(pat);
    fixture_advance_to(&fix, fix.now + 1);
    TEST_ASSERT_EQUAL_size_t(0U, count_couplings(topic));
    TEST_ASSERT_NULL(topic->sub_reader);
    TEST_ASSERT_FALSE(is_implicit(topic));
    const byte_t payload[4] = { 1, 2, 3, 4 };
    TEST_ASSERT_EQUAL_UINT8(CY_OK,
                            cy_publish(pub, fix.now + MEGA, (cy_bytes_t){ .size = sizeof(payload), .data = payload }));

    cy_future_t* const pat2 = cy_subscribe(fix.cy, cy_str("l/*"), 64U);
    TEST_ASSERT_NOT_NULL(pat2);
    TEST_ASSERT_EQUAL_size_t(1U, count_couplings(topic));

    cy_unadvertise(pub);
    TEST_ASSERT_TRUE(is_implicit(topic));
    fix.now += IMPLICIT_TOPIC_DEFAULT_TIMEOUT_us + MEGA;
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(fix.cy));
    TEST_ASSERT_EQUAL_UINT8(CY_OK, cy_spin_once(fix.cy));
    TEST_ASSERT_NULL(cy_topic_find_by_name(fix.cy, cy_str("l/a")));

    cy_future_destroy(pat2);
    fixture_teardown(&fix);
}

// With two matching patterns, a coupling OOM can leave a partial subset coupled (one root hears the topic, the other
// does not). The topic survives with an async error, and re-subscribing both patterns repairs the missing coupling.
static void test_partial_coupling_oom_reports_and_repairs(void)
{
    bool saw_partial = false;
    for (size_t n = 0U; (n < 64U) && !saw_partial; n++) {
        msg_fixture_t fix;
        fixture_init(&fix);
        async_error_sink_t sink = { 0U };
        cy_diag_t diag = { .next = NULL, .user_context = CY_USER_CONTEXT_EMPTY, .vtable = &async_error_counter_vtable };
        diag.user_context.ptr[0] = &sink;
        cy_diag_add(fix.cy, &diag);

        cy_future_t* const pat_one = cy_subscribe(fix.cy, cy_str("mp/*"), 64U);
        cy_future_t* const pat_any = cy_subscribe(fix.cy, cy_str("mp/>"), 64U);
        TEST_ASSERT_NOT_NULL(pat_one);
        TEST_ASSERT_NOT_NULL(pat_any);

        fix.new_alloc_count       = 0U;
        fix.fail_after            = n;
        cy_publisher_t* const pub = cy_advertise(fix.cy, cy_str("mp/t"));
        fix.fail_after            = SIZE_MAX;

        cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("mp/t"));
        if ((pub != NULL) && (topic != NULL) && (count_couplings(topic) == 1U)) {
            saw_partial = true;
            TEST_ASSERT_TRUE(sink.count > 0U);
            // Re-subscribing both patterns couples the missing root (idempotent for the one already coupled).
            cy_future_t* const rep_one = cy_subscribe(fix.cy, cy_str("mp/*"), 64U);
            cy_future_t* const rep_any = cy_subscribe(fix.cy, cy_str("mp/>"), 64U);
            TEST_ASSERT_NOT_NULL(rep_one);
            TEST_ASSERT_NOT_NULL(rep_any);
            TEST_ASSERT_EQUAL_size_t(2U, count_couplings(topic));
            inject_message(&fix, topic, false, 100U, 88U);
            TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat_one));
            TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat_any));
            cy_future_destroy(rep_one);
            cy_future_destroy(rep_any);
        }
        if (pub != NULL) {
            cy_unadvertise(pub);
        }
        cy_future_destroy(pat_one);
        cy_future_destroy(pat_any);
        fixture_teardown(&fix);
    }
    TEST_ASSERT_TRUE(saw_partial);
}

void setUp(void) {}
void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_advertise_then_pattern_no_double_coupling); // no-regression guard first: passes pre- and post-fix
    RUN_TEST(test_pattern_then_advertise_couples_multi_root);
    RUN_TEST(test_pattern_then_verbatim_subscribe_couples);
    RUN_TEST(test_substitutions_on_local_topic);
    RUN_TEST(test_pinned_local_advertise_couples);
    RUN_TEST(test_coupling_oom_keeps_topic);
    RUN_TEST(test_partial_coupling_oom_reports_and_repairs);
    RUN_TEST(test_lifecycle_decouple_and_retire);
    return UNITY_END();
}
