// Regression tests for M8: a reliable message no subscriber accepted on first delivery must not be recorded in the
// dedup filter, else its retransmit is falsely acked as a duplicate without ever being delivered. Drives the real
// cy_on_message path and captures outbound ACKs via the unicast hook.

#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include "intrusive_message_fixture.h"

// Vector 1, reordering slot OOM: the un-accepted tag must not be committed; the retransmit is delivered then acked.
static void test_reliable_delivered_after_slot_oom(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe_ordered(fix.cy, cy_str("m8/a"), 64U, 100 * KILO);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/a"));
    TEST_ASSERT_NOT_NULL(topic);

    // First message (first contact): interned, accepted, acked.
    inject_message(&fix, topic, true, 1000U, 10U);
    TEST_ASSERT_EQUAL_size_t(1U, fix.ack_count);
    TEST_ASSERT_EQUAL_UINT8(header_msg_ack, fix.acks[0].type);
    TEST_ASSERT_EQUAL_UINT64(1000U, fix.acks[0].tag);

    // tag 1002: slot interning OOMs -> not accepted, not acked, and the tag must not be recorded in dedup.
    fix.fail_after      = 0U;
    fix.new_alloc_count = 0U;
    inject_message(&fix, topic, true, 1002U, 20U);
    TEST_ASSERT_EQUAL_size_t(1U, fix.ack_count);
    TEST_ASSERT_FALSE(dedup_check(find_dedup(topic, UINT64_C(0xBEEF)), 1002U));
    fix.fail_after = SIZE_MAX;

    // Retransmit under no pressure: accepted (interned) and acked.
    inject_message(&fix, topic, true, 1002U, 20U);
    TEST_ASSERT_EQUAL_size_t(2U, fix.ack_count);
    TEST_ASSERT_EQUAL_UINT8(header_msg_ack, fix.acks[1].type);
    TEST_ASSERT_EQUAL_UINT64(1002U, fix.acks[1].tag);

    // After the window expires BOTH messages reach the app (pre-fix only tag 1000 did).
    fixture_advance_to(&fix, fix.now + (500 * KILO));
    TEST_ASSERT_EQUAL_UINT64(2U, cy_arrival_count(sub));

    cy_future_destroy(sub);
    fixture_teardown(&fix);
}

// Vector 1, reordering-state OOM (rr==NULL): dedup entry is created (its alloc precedes the state) but the tag must
// not be committed, so the retransmit is delivered rather than phantom-acked.
static void test_reliable_state_oom_then_delivered(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub_future = cy_subscribe_ordered(fix.cy, cy_str("m8/s"), 64U, 100 * KILO);
    TEST_ASSERT_NOT_NULL(sub_future);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/s"));
    TEST_ASSERT_NOT_NULL(topic);
    subscriber_t* const sub = topic_only_subscriber(topic);

    // Alloc order on first contact is dedup_t, reordering_t, slot; fail_after=1 fails the reordering_t alloc only.
    const uint64_t remote = UINT64_C(0xBEEF);
    fix.fail_after        = 1U;
    fix.new_alloc_count   = 0U;
    inject_message_from(&fix, topic, remote, true, 1000U, 10U);
    fix.fail_after = SIZE_MAX;

    // Pin the failure to the reordering-state alloc: dedup exists but recorded nothing, no reordering state, no ack.
    TEST_ASSERT_EQUAL_size_t(0U, fix.ack_count);
    dedup_t* const dd = find_dedup(topic, remote);
    TEST_ASSERT_NOT_NULL(dd);
    TEST_ASSERT_FALSE(dedup_check(dd, 1000U));
    TEST_ASSERT_NULL(find_reordering_state(sub, topic, remote));

    // Retransmit with memory available: accepted, acked, delivered.
    inject_message_from(&fix, topic, remote, true, 1000U, 10U);
    TEST_ASSERT_EQUAL_size_t(1U, fix.ack_count);
    TEST_ASSERT_EQUAL_UINT8(header_msg_ack, fix.acks[0].type);
    TEST_ASSERT_EQUAL_UINT64(1000U, fix.acks[0].tag);
    TEST_ASSERT_NOT_NULL(find_reordering_state(sub, topic, remote));

    fixture_advance_to(&fix, fix.now + (500 * KILO));
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub_future));

    cy_future_destroy(sub_future);
    fixture_teardown(&fix);
}

// Vector 1, all subscribers disposed (but still coupled): accepted by nobody, so never acked -- not on first delivery
// nor on any retransmit. Pre-fix the retransmit was phantom-acked because the first delivery committed the tag.
static void test_reliable_all_disposed_no_false_ack(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("m8/d"), 64U); // unordered reliable subscriber
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/d"));
    TEST_ASSERT_NOT_NULL(topic);

    // Dispose without spinning: stays coupled (disposed-but-not-destroyed), so on_message reaches dedup then skips it.
    cy_future_destroy(sub);
    TEST_ASSERT_NOT_NULL(topic->couplings);

    inject_message(&fix, topic, true, 1000U, 10U); // first delivery: skipped -> no ack
    TEST_ASSERT_EQUAL_size_t(0U, fix.ack_count);
    inject_message(&fix, topic, true, 1000U, 10U); // retransmit: must still NOT be acked
    TEST_ASSERT_EQUAL_size_t(0U, fix.ack_count);

    fixture_teardown(&fix);
}

// Multi-subscriber partial acceptance: two reliable subscribers on one topic, one disposed and one live. One
// acceptance is enough to commit+ack; the retransmit is then deduplicated without re-delivering.
static void test_reliable_multi_subscriber_partial_acceptance(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub_dead = cy_subscribe(fix.cy, cy_str("m8/m"), 64U);
    TEST_ASSERT_NOT_NULL(sub_dead);
    cy_future_t* const sub_live = cy_subscribe(fix.cy, cy_str("m8/m"), 64U);
    TEST_ASSERT_NOT_NULL(sub_live);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/m"));
    TEST_ASSERT_NOT_NULL(topic);

    cy_future_destroy(sub_dead); // disposed but still coupled -> skipped in the subscriber loop

    // The live subscriber accepts -> commit + exactly one positive ack; the disposed one is skipped.
    inject_message(&fix, topic, true, 1000U, 10U);
    TEST_ASSERT_EQUAL_size_t(1U, fix.ack_count);
    TEST_ASSERT_EQUAL_UINT8(header_msg_ack, fix.acks[0].type);
    TEST_ASSERT_EQUAL_UINT64(1000U, fix.acks[0].tag);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub_live));
    TEST_ASSERT_TRUE(dedup_check(find_dedup(topic, UINT64_C(0xBEEF)), 1000U)); // committed once

    // Retransmit: deduplicated -> acked again, not re-delivered.
    inject_message(&fix, topic, true, 1000U, 10U);
    TEST_ASSERT_EQUAL_size_t(2U, fix.ack_count);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub_live));

    cy_future_destroy(sub_live);
    fixture_teardown(&fix);
}

// No-regression guard: a genuine (already-delivered) duplicate is still acked without a second delivery.
static void test_reliable_genuine_duplicate_acked_once(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("m8/g"), 64U); // unordered: immediate delivery
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/g"));
    TEST_ASSERT_NOT_NULL(topic);

    inject_message(&fix, topic, true, 1000U, 10U); // delivered + acked
    TEST_ASSERT_EQUAL_size_t(1U, fix.ack_count);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub));

    inject_message(&fix, topic, true, 1000U, 10U); // genuine duplicate: acked again, NOT re-delivered
    TEST_ASSERT_EQUAL_size_t(2U, fix.ack_count);
    TEST_ASSERT_EQUAL_UINT8(header_msg_ack, fix.acks[1].type);
    TEST_ASSERT_EQUAL_UINT64(1000U, fix.acks[1].tag);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub)); // still one arrival

    cy_future_destroy(sub);
    fixture_teardown(&fix);
}

// Vector 2, reordering self-disposal: reordering_drop_stale ejects a stale interned message whose callback disposes
// this subscriber; the current message must then not be acked. Pre-fix reordering_push still returned true -> false
// ack.
static void test_reliable_reordering_self_disposal_no_false_ack(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe_ordered(fix.cy, cy_str("m8/x"), 64U, 50 * KILO);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/x"));
    TEST_ASSERT_NOT_NULL(topic);

    // Remote A (best-effort) interns a message in a reordering state; no delivery yet, and best-effort is never acked.
    const uint64_t remote_a = UINT64_C(0xA11CE);
    inject_message_from(&fix, topic, remote_a, false, 4000U, 30U);
    TEST_ASSERT_EQUAL_size_t(0U, fix.ack_count);

    cy_future_callback_set(sub, cy_future_destroy); // auto-dispose on first delivery

    fix.now += SESSION_LIFETIME + MEGA; // age state A stale without spinning, so its slot stays interned

    // Remote B (reliable): its drop_stale sweep ejects A's slot -> delivery -> callback disposes sub. B must not be
    // acked.
    const uint64_t remote_b = UINT64_C(0xB0B);
    const uint64_t tag_b    = 7000U;
    inject_message_from(&fix, topic, remote_b, true, tag_b, 40U);

    TEST_ASSERT_TRUE(((subscriber_t*)sub)->disposed);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub)); // only A delivered
    TEST_ASSERT_EQUAL_size_t(0U, count_acks_with_tag(&fix, tag_b));

    fixture_teardown(&fix); // sub already destroyed by the callback
}

// Vector 2b, self-disposal via a forced eject INSIDE reordering_push: a far-ahead reliable message force-ejects an
// interned slot whose callback disposes this sub; the current message must not be acked. Pre-fix reordering_push
// returned true after the disposal -> false ack.
static void test_reliable_reordering_push_eject_self_disposal_no_false_ack(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe_ordered(fix.cy, cy_str("m8/y"), 64U, 100 * KILO);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/y"));
    TEST_ASSERT_NOT_NULL(topic);

    // First contact (best-effort) interns tag 1000 (lin_tag 8); no delivery yet.
    const uint64_t remote = UINT64_C(0xBEEF);
    inject_message_from(&fix, topic, remote, false, 1000U, 10U);

    cy_future_callback_set(sub, cy_future_destroy); // auto-dispose on first delivery

    // Far-ahead reliable tag forces ejection of the interned slot (lin_tag > last_ejected + REORDERING_CAPACITY);
    // that eject delivers tag 1000 -> callback disposes sub -> the current far tag is handled on a disposed sub.
    const uint64_t tag_far = 1000U + 100U;
    inject_message_from(&fix, topic, remote, true, tag_far, 20U);

    TEST_ASSERT_TRUE(((subscriber_t*)sub)->disposed);
    TEST_ASSERT_EQUAL_size_t(0U, count_acks_with_tag(&fix, tag_far));

    fixture_teardown(&fix); // sub already destroyed by the callback
}

// Vector 2c, the same reordering_push guard reached via the OTHER forced-eject site: a far-backward restart tag
// triggers reordering_eject_all, whose delivery disposes this sub; the current message must not be acked.
static void test_reliable_reordering_push_backward_self_disposal_no_false_ack(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe_ordered(fix.cy, cy_str("m8/z"), 64U, 100 * KILO);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/z"));
    TEST_ASSERT_NOT_NULL(topic);

    // First contact (best-effort) at a high tag interns a slot; no delivery yet.
    const uint64_t remote = UINT64_C(0xBEEF);
    inject_message_from(&fix, topic, remote, false, UINT64_C(0x8000000000001000), 10U);

    cy_future_callback_set(sub, cy_future_destroy); // auto-dispose on first delivery

    // A far-backward restart tag (> SESSION_COUNTER_MAX_BACKWARD_LAG below the baseline) triggers reordering_eject_all,
    // which delivers the interned slot -> callback disposes sub -> the current reliable tag lands on a disposed sub.
    const uint64_t tag_back = UINT64_C(0x1000);
    inject_message_from(&fix, topic, remote, true, tag_back, 20U);

    TEST_ASSERT_TRUE(((subscriber_t*)sub)->disposed);
    TEST_ASSERT_EQUAL_size_t(0U, count_acks_with_tag(&fix, tag_back));

    fixture_teardown(&fix); // sub already destroyed by the callback
}

// A dedup entry created on a failed-acceptance receive is committed to nothing but must still be reaped by
// dedup_drop_stale (via the recency enlist that dedup_touch performs), not leaked until topic teardown.
static void test_reliable_uncommitted_dedup_entry_reaped(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe_ordered(fix.cy, cy_str("m8/l"), 64U, 100 * KILO);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/l"));
    TEST_ASSERT_NOT_NULL(topic);
    subscriber_t* const subr = topic_only_subscriber(topic);

    // Reordering-state OOM: the dedup entry is created (and touched) but the tag is not committed, and no state.
    const uint64_t remote = UINT64_C(0xBEEF);
    fix.fail_after        = 1U;
    fix.new_alloc_count   = 0U;
    inject_message_from(&fix, topic, remote, true, 1000U, 10U);
    fix.fail_after = SIZE_MAX;
    TEST_ASSERT_NOT_NULL(find_dedup(topic, remote));
    TEST_ASSERT_NULL(find_reordering_state(subr, topic, remote));

    // Age past SESSION_LIFETIME, then any later reliable receive drives dedup_drop_stale; the uncommitted entry,
    // enlisted only by dedup_touch, must be reaped.
    fix.now += SESSION_LIFETIME + MEGA;
    inject_message_from(&fix, topic, UINT64_C(0xF00D), true, 2000U, 20U);
    TEST_ASSERT_NULL(find_dedup(topic, remote));

    cy_future_destroy(sub);
    fixture_teardown(&fix);
}

// M8 flip side: a window-dropped reliable tag must keep being refused for as long as the remote retransmits it.
// Late retransmits must refresh the reordering-state recency; otherwise the state is reaped after SESSION_LIFETIME
// of no ACCEPTED traffic, and the next retransmit is resequenced as a fresh session -> the stale message is
// delivered out of order AND falsely acked.
static void test_reliable_late_retransmit_never_resurrected(void)
{
    msg_fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe_ordered(fix.cy, cy_str("m8/r"), 64U, 100 * KILO);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("m8/r"));
    TEST_ASSERT_NOT_NULL(topic);

    // Establish the session: tags 1000..1002 interned+acked, then ejected in order on window expiration.
    inject_message(&fix, topic, true, 1000U, 10U);
    inject_message(&fix, topic, true, 1001U, 11U);
    inject_message(&fix, topic, true, 1002U, 12U);
    TEST_ASSERT_EQUAL_size_t(3U, fix.ack_count);
    fixture_advance_to(&fix, fix.now + (200 * KILO));
    TEST_ASSERT_EQUAL_UINT64(3U, cy_arrival_count(sub));

    // Tag 995 maps below last_ejected_lin_tag: window-dropped, no ack. The publisher then retransmits it every
    // 10 s for 80 s total, far past SESSION_LIFETIME. Every retransmit must be refused: no ack, no delivery.
    const uint64_t tag_stale = 995U;
    for (size_t i = 0U; i < 8U; i++) {
        fix.now += 10 * MEGA;
        inject_message(&fix, topic, true, tag_stale, 99U);
        TEST_ASSERT_EQUAL_size_t(0U, count_acks_with_tag(&fix, tag_stale));
        TEST_ASSERT_EQUAL_UINT64(3U, cy_arrival_count(sub));
    }
    fixture_advance_to(&fix, fix.now + (200 * KILO)); // Would eject a wrongly interned stale slot.
    TEST_ASSERT_EQUAL_UINT64(3U, cy_arrival_count(sub));

    cy_future_destroy(sub);
    fixture_teardown(&fix);
}

void setUp(void) {}
void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_reliable_genuine_duplicate_acked_once); // no-regression guard first: passes pre- and post-fix
    RUN_TEST(test_reliable_delivered_after_slot_oom);
    RUN_TEST(test_reliable_state_oom_then_delivered);
    RUN_TEST(test_reliable_all_disposed_no_false_ack);
    RUN_TEST(test_reliable_multi_subscriber_partial_acceptance);
    RUN_TEST(test_reliable_reordering_self_disposal_no_false_ack);
    RUN_TEST(test_reliable_reordering_push_eject_self_disposal_no_false_ack);
    RUN_TEST(test_reliable_reordering_push_backward_self_disposal_no_false_ack);
    RUN_TEST(test_reliable_uncommitted_dedup_entry_reaped);
    RUN_TEST(test_reliable_late_retransmit_never_resurrected);
    return UNITY_END();
}
