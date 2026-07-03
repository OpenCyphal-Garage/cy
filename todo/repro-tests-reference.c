// ============================================================================================================
// REFERENCE SCAFFOLDING — NOT A BUILD TARGET. Lives under TODO/ on purpose; it is NOT registered in
// tests/CMakeLists.txt and is NOT compiled or run by ctest. It is a borrow-source for the per-defect regression
// tests described in the sibling TODO/<label>-*.md handoff files.
//
// The cases below intentionally assert the CURRENT (pre-fix, buggy) behavior to prove each defect exists.
// When implementing a fix, DO NOT re-register this file. Instead, copy the relevant fixture + case into the
// canonical test location named in that defect's handoff file (e.g. tests/src/test_intrusive_reordering.c,
// test_intrusive_dedup.c, tests/src/test_api_name.cpp, cy_can/tests/, cy_udp_posix/tests/, ...) and FLIP the
// assertion to require the FIXED behavior, so the regression fails on pre-fix code and passes after.
//
// Reusable bits worth borrowing: the full cy_new fixture, inject_message_from(), the ACK-capture unicast hook,
// and the subject_tracker helpers. The dedup-UAF case (test_dedup_factory_mutates_tree_during_insert) is the
// seed for C1 and needs AddressSanitizer to observe the corruption.
// See TODO/report-for-humans-only.html for the full findings context.
// ============================================================================================================

#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include "message.h"
#include "intrusive_fixture_utils.h"
#include <string.h>

#define ACK_CAPTURE_CAPACITY 32U

typedef struct
{
    byte_t   type;
    uint64_t tag;
    uint64_t hash;
} ack_capture_t;

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    guarded_heap_t       heap;
    cy_t*                cy;
    cy_us_t              now;
    uint64_t             rand_state;

    size_t fail_after;      ///< Fail N-th new allocation when new_alloc_count >= fail_after.
    size_t new_alloc_count; ///< Counts fresh allocations only.

    size_t        subject_send_count;
    size_t        pub_send_count;      ///< Counts only user message publications (header types 0 and 1).
    size_t        fail_pub_send_after; ///< Message publications fail with CY_ERR_MEDIA once the count exceeds this.
    size_t        unicast_send_count;
    size_t        ack_count;
    ack_capture_t acks[ACK_CAPTURE_CAPACITY];

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
    self->subject_send_count++;
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
    (void)lane;
    (void)deadline;
    fixture_t* const self = (fixture_t*)platform;
    self->unicast_send_count++;
    byte_t            header[HEADER_BYTES] = { 0 };
    size_t            copied               = 0U;
    const cy_bytes_t* frag                 = &message;
    while ((frag != NULL) && (copied < sizeof(header))) {
        if ((frag->size > 0U) && (frag->data != NULL)) {
            const size_t n = smaller(sizeof(header) - copied, frag->size);
            memcpy(&header[copied], frag->data, n);
            copied += n;
        }
        frag = frag->next;
    }
    if ((copied >= HEADER_BYTES) && ((header[0] == header_msg_ack) || (header[0] == header_msg_nack)) && //
        (self->ack_count < ACK_CAPTURE_CAPACITY)) {
        ack_capture_t* const ack = &self->acks[self->ack_count++];
        ack->type                = header[0];
        ack->hash                = deserialize_u64(&header[8]);
        ack->tag                 = deserialize_u64(&header[16]);
    }
    return CY_OK;
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

static void inject_message(fixture_t* const        self,
                           const cy_topic_t* const topic,
                           const bool              reliable,
                           const uint64_t          tag,
                           const byte_t            marker)
{
    inject_message_from(self, topic, UINT64_C(0xBEEF), reliable, tag, marker);
}

// --------------------------------------------------------------------------------------------------------------------
// FINDING 1: A reliable message that no subscriber managed to accept (e.g. OOM while interning in the reordering
// buffer) is recorded in the dedup filter anyway; the sender's retransmission is then classified as a duplicate and
// POSITIVELY ACKNOWLEDGED even though the application never received the message. The sender is told the message
// was delivered reliably while it was silently lost.
// --------------------------------------------------------------------------------------------------------------------
static void test_reliable_false_ack_after_failed_acceptance(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe_ordered(fix.cy, cy_str("repro/a"), 64U, 100 * KILO);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("repro/a"));
    TEST_ASSERT_NOT_NULL(topic);

    // First reliable message: interned in the reordering buffer (first contact), accepted, hence acked.
    inject_message(&fix, topic, true, 1000U, 10U);
    TEST_ASSERT_EQUAL_size_t(1U, fix.ack_count);
    TEST_ASSERT_EQUAL_UINT8(header_msg_ack, fix.acks[0].type);
    TEST_ASSERT_EQUAL_UINT64(1000U, fix.acks[0].tag);

    // Second reliable message, tag 1002 (out of order): interning fails due to OOM -> not accepted -> NOT acked. OK.
    fix.fail_after      = 0U; // All fresh allocations fail from now on.
    fix.new_alloc_count = 0U;
    inject_message(&fix, topic, true, 1002U, 20U);
    TEST_ASSERT_EQUAL_size_t(1U, fix.ack_count); // Correct: no ack for a message nobody accepted.
    fix.fail_after = SIZE_MAX;                   // Memory pressure is over.

    // The sender did not receive an ack, so it retransmits the same message. The dedup filter now claims the
    // message was seen before, and the stack POSITIVELY acknowledges it without delivering it to anyone.
    inject_message(&fix, topic, true, 1002U, 20U);
    TEST_ASSERT_EQUAL_size_t(2U, fix.ack_count);
    TEST_ASSERT_EQUAL_UINT8(header_msg_ack, fix.acks[1].type); // <-- BUG: positive ack for an undelivered message.
    TEST_ASSERT_EQUAL_UINT64(1002U, fix.acks[1].tag);

    // Let the reordering window expire and confirm the application only ever saw ONE message (tag 1000),
    // proving that tag 1002 was lost despite the positive acknowledgement sent to the publisher.
    fixture_advance_to(&fix, fix.now + (500 * KILO));
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(sub));

    cy_future_destroy(sub);
    fixture_teardown(&fix);
}

// --------------------------------------------------------------------------------------------------------------------
// FINDING 2: Destroying a subscriber future does not release it synchronously; the actual destruction is deferred
// to the next event-loop spin. An application that destroys all its subscribers and immediately calls cy_destroy()
// (as the documentation instructs) trips an assertion in debug builds and leaks the subscriber state in release
// builds. There is an undocumented requirement to spin the loop between the last future destruction and cy_destroy.
// --------------------------------------------------------------------------------------------------------------------
static void test_subscriber_destroy_requires_spin_before_cy_destroy(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("deferred/x"), 16U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_future_destroy(sub);

    // The subscriber root is still registered: cy_destroy() at this point would assert (debug) or leak (release).
    TEST_ASSERT_FALSE(wkv_is_empty(&fix.cy->subscribers_by_name));

    // Only after a spin does the deferred destruction complete.
    fixture_advance_to(&fix, fix.now + 1);
    TEST_ASSERT_TRUE(wkv_is_empty(&fix.cy->subscribers_by_name));

    fixture_teardown(&fix);
}

// --------------------------------------------------------------------------------------------------------------------
// FINDING 3: The first message(s) from every remote on an ordered subscription are delayed by the full reordering
// window even when they arrive perfectly in order, because the reordering state has no way to know whether the
// first observed tag is the beginning of the sequence. This start-up latency (equal to the reordering window,
// per remote) is not documented in the API.
// --------------------------------------------------------------------------------------------------------------------
static void test_ordered_subscription_first_contact_latency(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_us_t      window = 100 * KILO;
    cy_future_t* const sub    = cy_subscribe_ordered(fix.cy, cy_str("latency/x"), 64U, window);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("latency/x"));
    TEST_ASSERT_NOT_NULL(topic);

    // Three best-effort messages arrive back-to-back, perfectly in order.
    inject_message(&fix, topic, false, 500U, 1U);
    inject_message(&fix, topic, false, 501U, 5U);
    inject_message(&fix, topic, false, 502U, 9U);

    // Nothing is delivered to the application: everything is interned awaiting hypothetical predecessors.
    TEST_ASSERT_EQUAL_UINT64(0U, cy_arrival_count(sub));

    // Only after the full reordering window expires does the application see the messages.
    fixture_advance_to(&fix, fix.now + window + KILO);
    TEST_ASSERT_EQUAL_UINT64(3U, cy_arrival_count(sub));

    cy_future_destroy(sub);
    fixture_teardown(&fix);
}

// --------------------------------------------------------------------------------------------------------------------
// FINDING 4: A topic created locally (here: by a verbatim subscription; same applies to cy_advertise) after a
// matching pattern subscription already exists is never coupled to that pattern subscription. Pattern matching of
// existing subscriptions is only performed for topics learned from the network (gossip); local topic creation skips
// it. The result is order-dependent: pattern-then-verbatim leaves the pattern subscriber permanently blind to the
// topic, while verbatim-then-pattern works as expected.
// --------------------------------------------------------------------------------------------------------------------
static size_t count_couplings(const cy_topic_t* const topic)
{
    size_t                     count = 0U;
    const cy_topic_coupling_t* cpl   = topic->couplings;
    while (cpl != NULL) {
        count++;
        cpl = cpl->next;
    }
    return count;
}

static void test_pattern_subscriber_blind_to_later_local_topics(void)
{
    fixture_t fix;
    fixture_init(&fix);

    // Order A: pattern first, verbatim second. The pattern subscriber never couples to the topic.
    cy_future_t* const pat = cy_subscribe(fix.cy, cy_str("order/*"), 512U);
    TEST_ASSERT_NOT_NULL(pat);
    cy_future_t* const verb = cy_subscribe(fix.cy, cy_str("order/a"), 16U);
    TEST_ASSERT_NOT_NULL(verb);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("order/a"));
    TEST_ASSERT_NOT_NULL(topic);

    // Expected: 2 couplings (verbatim + pattern). Actual: 1 (verbatim only) -- the pattern root was never consulted.
    TEST_ASSERT_EQUAL_size_t(1U, count_couplings(topic)); // <-- BUG: should be 2.

    // Consequently a message on the topic reaches only the verbatim subscriber.
    inject_message(&fix, topic, false, 100U, 33U);
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(verb));
    TEST_ASSERT_EQUAL_UINT64(0U, cy_arrival_count(pat)); // <-- BUG: the pattern matches but receives nothing.

    // Order B (control): verbatim exists first, then the pattern subscription couples to it at creation time.
    cy_future_t* const pat2 = cy_subscribe(fix.cy, cy_str("order/>"), 512U);
    TEST_ASSERT_NOT_NULL(pat2);
    TEST_ASSERT_EQUAL_size_t(2U, count_couplings(topic)); // Pattern created later DOES couple.
    inject_message(&fix, topic, false, 101U, 44U);
    TEST_ASSERT_EQUAL_UINT64(2U, cy_arrival_count(verb));
    TEST_ASSERT_EQUAL_UINT64(1U, cy_arrival_count(pat2));
    TEST_ASSERT_EQUAL_UINT64(0U, cy_arrival_count(pat)); // Still blind.

    cy_future_destroy(pat);
    cy_future_destroy(pat2);
    cy_future_destroy(verb);
    fixture_teardown(&fix);
}

// --------------------------------------------------------------------------------------------------------------------
// FINDING 5: When a verbatim subscription coexists with a pattern subscription on the same topic, the verbatim
// subscriber's extent unconditionally overrides the (possibly much larger) pattern subscriber's extent in
// subscription_extent_w_overhead(). The transport reader extent is therefore never grown to accommodate the pattern
// subscriber, whose messages will be silently truncated to the verbatim subscriber's extent.
// --------------------------------------------------------------------------------------------------------------------
static void test_pattern_extent_starved_by_verbatim(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const verb = cy_subscribe(fix.cy, cy_str("ext/a"), 16U);
    TEST_ASSERT_NOT_NULL(verb);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("ext/a"));
    TEST_ASSERT_NOT_NULL(topic);
    TEST_ASSERT_NOT_NULL(topic->sub_reader);
    TEST_ASSERT_EQUAL_size_t(16U + HEADER_BYTES, topic->sub_reader->handle->extent);

    // A pattern subscriber requesting a much larger extent couples to the same topic...
    cy_future_t* const pat = cy_subscribe(fix.cy, cy_str("ext/*"), 4096U);
    TEST_ASSERT_NOT_NULL(pat);
    TEST_ASSERT_EQUAL_size_t(2U, count_couplings(topic));

    // ...but the reader extent is not grown: the verbatim extent takes precedence and the pattern subscriber
    // will receive messages truncated to 16 bytes. Expected: extent >= 4096 + HEADER_BYTES.
    TEST_ASSERT_EQUAL_size_t(16U + HEADER_BYTES, topic->sub_reader->handle->extent); // <-- pattern extent ignored

    cy_future_destroy(verb);
    cy_future_destroy(pat);
    fixture_teardown(&fix);
}

// --------------------------------------------------------------------------------------------------------------------
// FINDING 6: The documented auto-destroy idiom `cy_future_callback_set(future, cy_future_destroy)` (cy.h, README,
// example_file_server.c) destroys the future on the FIRST transient error notification while it is still pending,
// which by documented semantics cancels the reliable delivery operation: retransmissions cease permanently after a
// single failed send attempt, precisely when reliable delivery is most needed (congestion). The control run shows
// that without the transient failure the stack keeps retransmitting.
// --------------------------------------------------------------------------------------------------------------------
static void run_reliable_with_auto_destroy(fixture_t* const fix,
                                           const bool       fail_first_retransmit,
                                           size_t* const    out_sends)
{
    cy_publisher_t* const pub = cy_advertise(fix->cy, cy_str("auto/x"));
    TEST_ASSERT_NOT_NULL(pub);
    const byte_t       payload[4] = { 1, 2, 3, 4 };
    const cy_bytes_t   msg        = { .size = sizeof(payload), .data = payload };
    const cy_us_t      deadline   = fix->now + (10 * MEGA); // Plenty of time for several retransmissions.
    const size_t       base_sends = fix->pub_send_count;
    cy_future_t* const fut        = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);
    // Arrange for the first retransmission (the second message send overall) to fail with a transient error.
    fix->fail_pub_send_after = fail_first_retransmit ? fix->pub_send_count : SIZE_MAX;
    cy_future_callback_set(fut, cy_future_destroy); // The documented "fire and forget" idiom.
    // Spin past the deadline in small steps so every retransmission event fires.
    const cy_us_t end = deadline + (100 * KILO);
    while (fix->now < end) {
        fixture_advance_to(fix, fix->now + (50 * KILO));
    }
    *out_sends               = fix->pub_send_count - base_sends;
    fix->fail_pub_send_after = SIZE_MAX;
    cy_unadvertise(pub);
}

static void test_auto_destroy_idiom_cancels_reliable_delivery_on_transient_error(void)
{
    fixture_t fix;
    fixture_init(&fix);

    // Control: no send failures; the stack retransmits several times until the deadline.
    size_t control_sends = 0U;
    run_reliable_with_auto_destroy(&fix, false, &control_sends);
    TEST_ASSERT_TRUE(control_sends >= 4U); // Initial + several retransmissions over 10 seconds.

    // Experiment: the first RETRANSMISSION fails transiently (e.g. transport queue momentarily full).
    // The transient error notification fires while the future is pending; the auto-destroy callback kills it,
    // cancelling the whole reliable delivery. Only the initial send and the one failed retransmit are observed;
    // the remaining ~10 seconds of budget are never used.
    size_t failing_sends = 0U;
    run_reliable_with_auto_destroy(&fix, true, &failing_sends);
    TEST_ASSERT_EQUAL_size_t(2U, failing_sends); // <-- Delivery abandoned after one transient failure.

    fixture_teardown(&fix);
}

// --------------------------------------------------------------------------------------------------------------------
// FINDING 7 (CRITICAL): dedup_factory() calls dedup_drop_stale() which removes and frees nodes from the SAME AVL tree
// that cavl2_find_or_insert() is currently inserting into. cavl2_find_or_insert() captures the parent slot pointer
// before invoking the factory; the factory's removals rebalance/free tree nodes, invalidating that captured pointer,
// so the subsequent write-through corrupts the heap. Best observed under AddressSanitizer as a heap-use-after-free.
// Trigger: a topic accumulates several reliable-publisher dedup entries; they all go stale (> SESSION_LIFETIME) while
// the per-topic GC (which only runs one topic per poll spin) has not yet swept this topic; then a reliable message
// from a NEW remote arrives and its dedup insertion triggers the in-factory stale purge.
// --------------------------------------------------------------------------------------------------------------------
static void test_dedup_factory_mutates_tree_during_insert(void)
{
    fixture_t fix;
    fixture_init(&fix);

    cy_future_t* const sub = cy_subscribe(fix.cy, cy_str("uaf/x"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("uaf/x"));
    TEST_ASSERT_NOT_NULL(topic);

    // Populate the per-remote dedup tree with several entries at the initial timestamp. Spread the remote-IDs so the
    // tree has some depth. Note: we deliberately do NOT call cy_spin_until (which would sweep stale dedup entries),
    // only cy_on_message, so the entries persist until the in-factory purge fires.
    const uint64_t remotes[] = { 50, 20, 80, 10, 30, 70, 90, 40, 60 };
    for (size_t i = 0; i < (sizeof(remotes) / sizeof(remotes[0])); i++) {
        inject_message_from(&fix, topic, remotes[i], true, 1000U + i, (byte_t)(i + 1U));
    }

    // Let all those entries become stale.
    fix.now += SESSION_LIFETIME + MEGA;

    // A reliable message from a brand-new remote now inserts into the dedup tree; dedup_factory -> dedup_drop_stale
    // removes+frees the stale nodes mid-insert. Under ASan this reports heap-use-after-free inside
    // cavl2_find_or_insert; without ASan it may corrupt the heap silently or trip a later assertion.
    inject_message_from(&fix, topic, 999U, true, 5000U, 0xAAU);

    cy_future_destroy(sub);
    fixture_teardown(&fix);
}

// --------------------------------------------------------------------------------------------------------------------
// FINDING 8 (HIGH): An ordered subscription permanently blackholes a remote after that remote restarts, with ~50%
// probability. Reordering linearizes tags against a baseline frozen at first contact. A restart re-randomizes the
// remote's tag counter; if the new baseline lands in the "backward" half-space (lin_tag > INT64_MAX), every message
// is dropped as a late/backward straggler. Because reordering_push() refreshes the recency timestamp BEFORE the
// backward-drop check, the wedged state never goes stale and the staleness GC never rebuilds it -> permanent loss.
// --------------------------------------------------------------------------------------------------------------------
static void test_ordered_subscription_blackholes_after_remote_restart(void)
{
    fixture_t fix;
    fixture_init(&fix);

    const cy_us_t      window = 50 * KILO;
    cy_future_t* const sub    = cy_subscribe_ordered(fix.cy, cy_str("restart/x"), 64U, window);
    TEST_ASSERT_NOT_NULL(sub);
    cy_topic_t* const topic = cy_topic_find_by_name(fix.cy, cy_str("restart/x"));
    TEST_ASSERT_NOT_NULL(topic);

    // Establish a stream from remote R with a high baseline tag, and let it eject so last_ejected advances.
    const uint64_t R        = 0x1234U;
    const uint64_t high_tag = UINT64_C(0x8000000000000000); // baseline for the "before restart" epoch
    for (uint64_t i = 0; i < 4U; i++) {
        inject_message_from(&fix, topic, R, false, high_tag + i, (byte_t)(i + 1U));
    }
    fix.now += window + KILO;
    fixture_advance_to(&fix, fix.now); // flush interned via window expiry
    const uint64_t delivered_before = cy_arrival_count(sub);
    TEST_ASSERT_TRUE(delivered_before >= 1U);

    // Remote R restarts and picks a fresh random baseline that lands in the backward half-space relative to the old
    // baseline (old_baseline was ~high_tag - CAPACITY/2; a new tag < old baseline linearizes to lin_tag > INT64_MAX).
    const uint64_t restart_tag = UINT64_C(0x0000000000001000); // well below the old baseline
    for (uint64_t i = 0; i < 20U; i++) {
        // Advance time each message; if the state went stale it would be rebuilt, but the recency refresh prevents it.
        fix.now += KILO;
        inject_message_from(&fix, topic, R, false, restart_tag + i, (byte_t)(i + 100U));
    }
    // Advance well past SESSION_LIFETIME and give the reordering GC a chance (would need a poll sweep of this topic).
    fix.now += SESSION_LIFETIME + MEGA;
    fixture_advance_to(&fix, fix.now);

    // The post-restart messages are all blackholed; delivered count did not advance despite 20 in-order messages.
    TEST_ASSERT_EQUAL_UINT64(delivered_before, cy_arrival_count(sub)); // <-- BUG: permanent blackhole after restart.

    cy_future_destroy(sub);
    fixture_teardown(&fix);
}

void setUp(void) {}
void tearDown(void) {}

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_reliable_false_ack_after_failed_acceptance);
    RUN_TEST(test_subscriber_destroy_requires_spin_before_cy_destroy);
    RUN_TEST(test_ordered_subscription_first_contact_latency);
    RUN_TEST(test_pattern_subscriber_blind_to_later_local_topics);
    RUN_TEST(test_pattern_extent_starved_by_verbatim);
    RUN_TEST(test_auto_destroy_idiom_cancels_reliable_delivery_on_transient_error);
    RUN_TEST(test_ordered_subscription_blackholes_after_remote_restart);
    // This test deliberately corrupts the heap to demonstrate the CRITICAL dedup-factory AVL-mutation defect.
    // It is excluded from the default registered suite (it crashes) and is intended to be run standalone under
    // AddressSanitizer via -DCY_REVIEW_RUN_UNSAFE. See the review report.
#ifdef CY_REVIEW_RUN_UNSAFE
    RUN_TEST(test_dedup_factory_mutates_tree_during_insert);
#else
    (void)test_dedup_factory_mutates_tree_during_insert;
#endif
    return UNITY_END();
}
