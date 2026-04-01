#include <cy.c> // NOLINT(bugprone-suspicious-include)
#include <unity.h>
#include "guarded_heap.h"
#include "intrusive_fixture_utils.h"
#include "message.h"
#include <stddef.h>
#include <string.h>

typedef struct
{
    cy_platform_t        platform;
    cy_platform_vtable_t vtable;
    guarded_heap_t       core_heap;
    guarded_heap_t       message_heap;
    cy_t*                cy;

    cy_us_t  now;
    uint64_t random_state;
    size_t   fail_after;
    size_t   new_alloc_count;
    size_t   fail_size;
    size_t   fail_size_count;
    uint8_t  fail_multicast_header;
    size_t   fail_multicast_count;
    uint8_t  fail_unicast_header;
    size_t   fail_unicast_count;
    cy_err_t fail_send_error;
    size_t   multicast_count;
    size_t   unicast_count;
    cy_us_t  unicast_extent;
    size_t   async_error_count;
    cy_err_t last_async_error;
    uint16_t last_async_error_line;

    uint8_t last_multicast_header;
    uint8_t last_unicast_header;
    byte_t  last_multicast[HEADER_BYTES];
    size_t  last_multicast_size;
    byte_t  last_unicast[HEADER_BYTES + 16U];
    size_t  last_unicast_size;

    subject_tracker_t active_readers;
    subject_tracker_t active_writers;
} fixture_t;

typedef struct
{
    size_t   calls;
    bool     saw_done;
    bool     saw_pending;
    cy_err_t last_error;
} destroy_capture_t;

static void flatten_fragments(byte_t* const    out,
                              const size_t     out_size,
                              const cy_bytes_t message,
                              size_t* const    out_copied)
{
    size_t copied = 0U;
    for (const cy_bytes_t* seg = &message; (seg != NULL) && (copied < out_size); seg = seg->next) {
        if ((seg->size == 0U) || (seg->data == NULL)) {
            continue;
        }
        const size_t to_copy = smaller(seg->size, out_size - copied);
        memcpy(&out[copied], seg->data, to_copy);
        copied += to_copy;
    }
    if (out_copied != NULL) {
        *out_copied = copied;
    }
}

static fixture_t* fixture_from(cy_platform_t* const platform) { return (fixture_t*)platform; }

static const fixture_t* fixture_from_const(const cy_platform_t* const platform) { return (const fixture_t*)platform; }

static void* fixture_realloc(cy_platform_t* const platform, void* const ptr, const size_t size)
{
    fixture_t* const self = fixture_from(platform);
    if ((ptr == NULL) && (size > 0U)) {
        if (self->new_alloc_count >= self->fail_after) {
            return NULL;
        }
        if ((self->fail_size_count > 0U) && (self->fail_size == size)) {
            self->fail_size_count--;
            return NULL;
        }
        self->new_alloc_count++;
    }
    return guarded_heap_realloc(&self->core_heap, ptr, size);
}

static cy_subject_writer_t* fixture_subject_writer_new(cy_platform_t* const platform, const uint32_t subject_id)
{
    fixture_t* const           self = fixture_from(platform);
    cy_subject_writer_t* const w    = intrusive_subject_writer_new(&self->core_heap, subject_id);
    if (w != NULL) {
        subject_tracker_add(&self->active_writers, subject_id);
    }
    return w;
}

static void fixture_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const writer)
{
    fixture_t* const self = fixture_from(platform);
    subject_tracker_remove(&self->active_writers, writer->subject_id);
    intrusive_subject_writer_destroy(&self->core_heap, writer);
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
    fixture_t* const self = fixture_from(platform);
    self->multicast_count++;
    memset(self->last_multicast, 0, sizeof(self->last_multicast));
    flatten_fragments(self->last_multicast, sizeof(self->last_multicast), message, &self->last_multicast_size);
    self->last_multicast_header = (self->last_multicast_size > 0U) ? (self->last_multicast[0]) : 0xFFU;
    if ((self->fail_multicast_count > 0U) && (self->last_multicast_header == self->fail_multicast_header)) {
        self->fail_multicast_count--;
        return self->fail_send_error;
    }
    return CY_OK;
}

static cy_subject_reader_t* fixture_subject_reader_new(cy_platform_t* const platform,
                                                       const uint32_t       subject_id,
                                                       const size_t         extent)
{
    fixture_t* const           self = fixture_from(platform);
    cy_subject_reader_t* const r    = intrusive_subject_reader_new(&self->core_heap, subject_id, extent);
    if (r != NULL) {
        subject_tracker_add(&self->active_readers, subject_id);
    }
    return r;
}

static void fixture_subject_reader_extent_set(cy_platform_t* const       platform,
                                              cy_subject_reader_t* const reader,
                                              const size_t               extent)
{
    fixture_t* const self = fixture_from(platform);
    subject_tracker_assert_contains(&self->active_readers, reader->subject_id);
    intrusive_subject_reader_extent_set(reader, extent);
}

static void fixture_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const reader)
{
    fixture_t* const self = fixture_from(platform);
    subject_tracker_remove(&self->active_readers, reader->subject_id);
    intrusive_subject_reader_destroy(&self->core_heap, reader);
}

static cy_err_t fixture_unicast_send(cy_platform_t* const   platform,
                                     const cy_lane_t* const lane,
                                     const cy_us_t          deadline,
                                     const cy_bytes_t       message)
{
    (void)lane;
    (void)deadline;
    fixture_t* const self = fixture_from(platform);
    self->unicast_count++;
    memset(self->last_unicast, 0, sizeof(self->last_unicast));
    flatten_fragments(self->last_unicast, sizeof(self->last_unicast), message, &self->last_unicast_size);
    self->last_unicast_header = (self->last_unicast_size > 0U) ? (self->last_unicast[0]) : 0xFFU;
    if ((self->fail_unicast_count > 0U) && (self->last_unicast_header == self->fail_unicast_header)) {
        self->fail_unicast_count--;
        return self->fail_send_error;
    }
    return CY_OK;
}

static void fixture_unicast_extent_set(cy_platform_t* const platform, const size_t extent)
{
    fixture_t* const self = fixture_from(platform);
    self->unicast_extent  = (cy_us_t)extent;
}

static cy_err_t fixture_spin(cy_platform_t* const platform, const cy_us_t deadline)
{
    (void)platform;
    (void)deadline;
    return CY_OK;
}

static cy_us_t fixture_now(cy_platform_t* const platform) { return fixture_from_const(platform)->now; }

static uint64_t fixture_random(cy_platform_t* const platform)
{
    fixture_t* const self = fixture_from(platform);
    self->random_state += UINT64_C(0x9E3779B97F4A7C15);
    return self->random_state;
}

static void fixture_async_error_handler(cy_t* const       cy,
                                        cy_topic_t* const topic,
                                        const cy_err_t    error,
                                        const uint16_t    line_number)
{
    (void)topic;
    fixture_t* const self = fixture_from(cy->platform);
    self->async_error_count++;
    self->last_async_error      = error;
    self->last_async_error_line = line_number;
}

static void fixture_init(fixture_t* const self)
{
    memset(self, 0, sizeof(*self));
    guarded_heap_init(&self->core_heap, UINT64_C(0xA0B1C2D3E4F56789));
    guarded_heap_init(&self->message_heap, UINT64_C(0x1021324354657687));

    self->now                              = 1000;
    self->random_state                     = UINT64_C(0x1122334455667788);
    self->fail_after                       = SIZE_MAX;
    self->fail_send_error                  = CY_ERR_MEDIA;
    self->fail_multicast_header            = 0xFFU;
    self->fail_unicast_header              = 0xFFU;
    self->last_multicast_header            = 0xFFU;
    self->last_unicast_header              = 0xFFU;
    self->last_async_error                 = CY_OK;
    self->last_async_error_line            = 0U;
    self->platform.vtable                  = &self->vtable;
    self->platform.cy                      = NULL;
    self->platform.subject_id_modulus      = (uint32_t)CY_SUBJECT_ID_MODULUS_16bit;
    self->vtable.realloc                   = fixture_realloc;
    self->vtable.subject_writer_new        = fixture_subject_writer_new;
    self->vtable.subject_writer_destroy    = fixture_subject_writer_destroy;
    self->vtable.subject_writer_send       = fixture_subject_writer_send;
    self->vtable.subject_reader_new        = fixture_subject_reader_new;
    self->vtable.subject_reader_extent_set = fixture_subject_reader_extent_set;
    self->vtable.subject_reader_destroy    = fixture_subject_reader_destroy;
    self->vtable.unicast                   = fixture_unicast_send;
    self->vtable.unicast_extent_set        = fixture_unicast_extent_set;
    self->vtable.spin                      = fixture_spin;
    self->vtable.now                       = fixture_now;
    self->vtable.random                    = fixture_random;

    self->cy = cy_new(&self->platform, cy_str("test"), (cy_str_t){ 0, NULL });
    TEST_ASSERT_NOT_NULL(self->cy);
    cy_async_error_handler_set(self->cy, fixture_async_error_handler);
}

static void fixture_spin_to(fixture_t* const self, const cy_us_t now)
{
    self->now = now;
    TEST_ASSERT_EQUAL_INT(CY_OK, cy_spin_once(self->cy));
}

static void fixture_fail_multicast_header(fixture_t* const self,
                                          const uint8_t    header_type,
                                          const size_t     count,
                                          const cy_err_t   error)
{
    self->fail_multicast_header = header_type;
    self->fail_multicast_count  = count;
    self->fail_send_error       = error;
}

static void fixture_fail_unicast_header(fixture_t* const self,
                                        const uint8_t    header_type,
                                        const size_t     count,
                                        const cy_err_t   error)
{
    self->fail_unicast_header = header_type;
    self->fail_unicast_count  = count;
    self->fail_send_error     = error;
}

static void fixture_fail_alloc_size(fixture_t* const self, const size_t size, const size_t count)
{
    self->fail_size       = size;
    self->fail_size_count = count;
}

static void fixture_deinit(fixture_t* const self)
{
    if (self->cy != NULL) {
        cy_destroy(self->cy);
        self->cy = NULL;
    }
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self->message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self->message_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_fragments(&self->core_heap));
    TEST_ASSERT_EQUAL_size_t(0U, guarded_heap_allocated_bytes(&self->core_heap));
}

static cy_message_ts_t make_wire_message(fixture_t* const    self,
                                         const byte_t* const data,
                                         const size_t        size,
                                         const cy_us_t       ts)
{
    cy_message_t* const msg = cy_test_message_make(&self->message_heap, data, size);
    TEST_ASSERT_NOT_NULL(msg);
    return (cy_message_ts_t){ .timestamp = ts, .content = msg };
}

static cy_lane_t make_lane(const uint64_t remote_id, const cy_prio_t prio)
{
    cy_lane_t lane = { 0 };
    lane.id        = remote_id;
    lane.prio      = prio;
    memcpy(lane.ctx.state, &lane.id, smaller(sizeof(lane.ctx.state), sizeof(lane.id)));
    return lane;
}

static void dispatch_publish_ack(fixture_t* const self,
                                 const uint64_t   remote_id,
                                 const uint64_t   topic_hash,
                                 const uint64_t   message_tag,
                                 const cy_us_t    ts)
{
    byte_t wire[HEADER_BYTES] = { 0 };
    wire[0]                   = header_msg_ack;
    (void)serialize_u32(&wire[4], 0U);
    (void)serialize_u64(&wire[8], topic_hash);
    (void)serialize_u64(&wire[16], message_tag);
    const cy_message_ts_t mts = make_wire_message(self, wire, sizeof(wire), ts);
    cy_on_message(&self->platform, make_lane(remote_id, cy_prio_nominal), NULL, mts);
}

static void dispatch_subscriber_message(fixture_t* const    self,
                                        const cy_topic_t*   topic,
                                        const uint64_t      remote_id,
                                        const uint8_t       header_type,
                                        const uint64_t      tag,
                                        const unsigned char payload_byte,
                                        const cy_us_t       ts)
{
    byte_t wire[HEADER_BYTES + 1U] = { 0 };
    wire[0]                        = (byte_t)(header_type);
    (void)serialize_u32(&wire[4], 0U);
    (void)serialize_u64(&wire[8], cy_topic_hash(topic));
    (void)serialize_u64(&wire[16], tag);
    wire[HEADER_BYTES]           = payload_byte;
    const cy_message_ts_t mts    = make_wire_message(self, wire, sizeof(wire), ts);
    cy_subject_reader_t   reader = { .subject_id = topic_subject_id((cy_topic_t*)topic) };
    cy_on_message(&self->platform, make_lane(remote_id, cy_prio_nominal), &reader.subject_id, mts);
}

static void dispatch_response_message(fixture_t* const    self,
                                      const uint64_t      remote_id,
                                      const uint8_t       header_type,
                                      const uint8_t       response_tag,
                                      const uint64_t      seqno,
                                      const uint64_t      topic_hash,
                                      const uint64_t      message_tag,
                                      const unsigned char payload_byte,
                                      const cy_us_t       ts)
{
    byte_t wire[HEADER_BYTES + 1U] = { 0 };
    wire[0]                        = (byte_t)(header_type);
    wire[1]                        = response_tag;
    (void)serialize_u48(&wire[2], seqno);
    (void)serialize_u64(&wire[8], topic_hash);
    (void)serialize_u64(&wire[16], message_tag);
    wire[HEADER_BYTES]        = payload_byte;
    const cy_message_ts_t mts = make_wire_message(self, wire, sizeof(wire), ts);
    cy_on_message(&self->platform, make_lane(remote_id, cy_prio_nominal), NULL, mts);
}

static void dispatch_response_ack(fixture_t* const self,
                                  const uint64_t   remote_id,
                                  const uint8_t    header_type,
                                  const uint8_t    response_tag,
                                  const uint64_t   seqno,
                                  const uint64_t   topic_hash,
                                  const uint64_t   message_tag,
                                  const cy_us_t    ts)
{
    byte_t wire[HEADER_BYTES] = { 0 };
    wire[0]                   = (byte_t)(header_type);
    wire[1]                   = response_tag;
    (void)serialize_u48(&wire[2], seqno);
    (void)serialize_u64(&wire[8], topic_hash);
    (void)serialize_u64(&wire[16], message_tag);
    const cy_message_ts_t mts = make_wire_message(self, wire, sizeof(wire), ts);
    cy_on_message(&self->platform, make_lane(remote_id, cy_prio_nominal), NULL, mts);
}

static void destroy_on_notify(cy_future_t* const fut)
{
    destroy_capture_t* const capture = (destroy_capture_t*)cy_future_context(fut).ptr[0];
    TEST_ASSERT_NOT_NULL(capture);
    capture->calls++;
    const bool done     = cy_future_done(fut);
    capture->last_error = cy_future_error(fut);
    capture->saw_done |= done;
    capture->saw_pending = capture->saw_pending || !done;

    const cy_t* const owner = fut->cy;
    cy_future_destroy(fut);
    void* const churn = mem_alloc(owner, 23U);
    mem_free(owner, churn);
}

static void set_destroy_callback(cy_future_t* const future, destroy_capture_t* const capture)
{
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = capture;
    cy_future_context_set(future, ctx);
    cy_future_callback_set(future, destroy_on_notify);
}

static uint64_t last_outgoing_tag_multicast(const fixture_t* const self)
{
    TEST_ASSERT_TRUE(self->last_multicast_size >= HEADER_BYTES);
    return deserialize_u64(&self->last_multicast[16]);
}

static uint64_t last_outgoing_hash_multicast(const fixture_t* const self)
{
    TEST_ASSERT_TRUE(self->last_multicast_size >= HEADER_BYTES);
    return deserialize_u64(&self->last_multicast[8]);
}

static uint8_t last_outgoing_rsp_tag(const fixture_t* const self)
{
    TEST_ASSERT_TRUE(self->last_unicast_size >= HEADER_BYTES);
    return self->last_unicast[1];
}

static uint64_t last_outgoing_rsp_seqno(const fixture_t* const self)
{
    TEST_ASSERT_TRUE(self->last_unicast_size >= HEADER_BYTES);
    return deserialize_u48(&self->last_unicast[2]);
}

static uint64_t last_outgoing_rsp_hash(const fixture_t* const self)
{
    TEST_ASSERT_TRUE(self->last_unicast_size >= HEADER_BYTES);
    return deserialize_u64(&self->last_unicast[8]);
}

static uint64_t last_outgoing_rsp_message_tag(const fixture_t* const self)
{
    TEST_ASSERT_TRUE(self->last_unicast_size >= HEADER_BYTES);
    return deserialize_u64(&self->last_unicast[16]);
}

static void test_publish_notify_ack_completion_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise(fixture.cy, cy_str("notify/publish/ack"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);

    const cy_bytes_t   msg = { .size = 1U, .data = "A", .next = NULL };
    cy_future_t* const fut = cy_publish_reliable(pub, fixture.now + 100000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    dispatch_publish_ack(&fixture,
                         UINT64_C(0xA001),
                         last_outgoing_hash_multicast(&fixture),
                         last_outgoing_tag_multicast(&fixture),
                         fixture.now);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_OK, cap.last_error);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_publish_notify_timeout_completion_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise(fixture.cy, cy_str("notify/publish/timeout"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_us_t      deadline = fixture.now + 4000;
    const cy_bytes_t   msg      = { .size = 1U, .data = "B", .next = NULL };
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    fixture_spin_to(&fixture, deadline + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cap.last_error);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_publish_notify_pending_media_error_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise(fixture.cy, cy_str("notify/publish/pending_media"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_bytes_t   msg = { .size = 1U, .data = "C", .next = NULL };
    cy_future_t* const fut = cy_publish_reliable(pub, fixture.now + 120000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    fixture_fail_multicast_header(&fixture, header_msg_rel, 1U, CY_ERR_MEDIA);
    fixture_spin_to(&fixture, fixture.now + cy_ack_timeout(pub) + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_pending);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, cap.last_error);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, fixture.last_async_error);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_publish_notify_pending_lag_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise(fixture.cy, cy_str("notify/publish/pending_lag"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_bytes_t   msg      = { .size = 1U, .data = "D", .next = NULL };
    const cy_us_t      deadline = fixture.now + 120000;
    cy_future_t* const fut      = cy_publish_reliable(pub, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    fixture_spin_to(&fixture, deadline - cy_ack_timeout(pub) + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_pending);
    TEST_ASSERT_EQUAL_INT(CY_ERR_LAG, cap.last_error);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_publish_callback_set_after_done_immediate_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise(fixture.cy, cy_str("notify/publish/immediate"));
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_bytes_t   msg = { .size = 1U, .data = "E", .next = NULL };
    cy_future_t* const fut = cy_publish_reliable(pub, fixture.now + 100000, msg);
    TEST_ASSERT_NOT_NULL(fut);
    dispatch_publish_ack(&fixture,
                         UINT64_C(0xA005),
                         last_outgoing_hash_multicast(&fixture),
                         last_outgoing_tag_multicast(&fixture),
                         fixture.now);
    TEST_ASSERT_TRUE(cy_future_done(fut));

    destroy_capture_t cap = { 0 };
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &cap;
    cy_future_context_set(fut, ctx);
    cy_future_callback_set(fut, destroy_on_notify);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_request_notify_publish_pending_error_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise_client(fixture.cy, cy_str("notify/request/publish_pending"), 16U);
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_bytes_t   msg = { .size = 1U, .data = "F", .next = NULL };
    cy_future_t* const fut = cy_request(pub, fixture.now + 120000, 50000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    fixture_fail_multicast_header(&fixture, header_msg_rel, 1U, CY_ERR_MEDIA);
    fixture_spin_to(&fixture, fixture.now + cy_ack_timeout(pub) + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_pending);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, cap.last_error);
    TEST_ASSERT_EQUAL_size_t(1U, fixture.async_error_count);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, fixture.last_async_error);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_request_notify_publish_done_fatal_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise_client(fixture.cy, cy_str("notify/request/publish_done"), 16U);
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_bytes_t   msg          = { .size = 1U, .data = "G", .next = NULL };
    const cy_us_t      req_deadline = fixture.now + 3000;
    cy_future_t* const fut          = cy_request(pub, req_deadline, 50000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    fixture_spin_to(&fixture, req_deadline + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cap.last_error);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_request_notify_on_response_best_effort_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise_client(fixture.cy, cy_str("notify/request/rsp_be"), 16U);
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_bytes_t   msg = { .size = 1U, .data = "H", .next = NULL };
    cy_future_t* const fut = cy_request(pub, fixture.now + 150000, 60000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    dispatch_response_message(&fixture,
                              UINT64_C(0xB001),
                              header_rsp_be,
                              0x11U,
                              0U,
                              last_outgoing_hash_multicast(&fixture),
                              last_outgoing_tag_multicast(&fixture),
                              0xABU,
                              fixture.now + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_OK, cap.last_error);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_request_notify_on_response_reliable_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise_client(fixture.cy, cy_str("notify/request/rsp_rel"), 16U);
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_bytes_t   msg = { .size = 1U, .data = "I", .next = NULL };
    cy_future_t* const fut = cy_request(pub, fixture.now + 150000, 60000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    dispatch_response_message(&fixture,
                              UINT64_C(0xB002),
                              header_rsp_rel,
                              0x12U,
                              0U,
                              last_outgoing_hash_multicast(&fixture),
                              last_outgoing_tag_multicast(&fixture),
                              0xACU,
                              fixture.now + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_OK, cap.last_error);
    fixture_spin_to(&fixture, fixture.now + (SESSION_LIFETIME / 2) + 1);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_request_notify_on_response_reliable_oom_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise_client(fixture.cy, cy_str("notify/request/rsp_oom"), 16U);
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_bytes_t   msg = { .size = 1U, .data = "J", .next = NULL };
    cy_future_t* const fut = cy_request(pub, fixture.now + 150000, 60000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    fixture_fail_alloc_size(&fixture, sizeof(request_future_remote_t), 1U);
    dispatch_response_message(&fixture,
                              UINT64_C(0xB003),
                              header_rsp_rel,
                              0x13U,
                              0U,
                              last_outgoing_hash_multicast(&fixture),
                              last_outgoing_tag_multicast(&fixture),
                              0xADU,
                              fixture.now + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, cap.last_error);
    TEST_ASSERT_TRUE(fixture.async_error_count > 0U);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, fixture.last_async_error);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static request_future_t* make_request_future_manual(fixture_t* const  fixture,
                                                    cy_topic_t* const topic,
                                                    const uint64_t    key,
                                                    const cy_us_t     timeout)
{
    memset(topic, 0, sizeof(*topic));
    topic->cy                   = fixture->cy;
    request_future_t* const out = future_new(fixture->cy, &request_future_vtable, sizeof(request_future_t));
    TEST_ASSERT_NOT_NULL(out);
    out->topic                           = topic;
    out->liveness_timeout                = timeout;
    out->last_response.message.timestamp = BIG_BANG;
    out->last_response.message.content   = NULL;
    const bool ok                        = future_index_insert(&out->base, &topic->request_futures_by_tag, key);
    TEST_ASSERT_TRUE(ok);
    future_deadline_arm(&out->base, fixture->now + timeout);
    return out;
}

static void test_request_notify_timeout_no_remote_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t        topic;
    request_future_t* fut = make_request_future_manual(&fixture, &topic, UINT64_C(0xCC01), 1000);
    destroy_capture_t cap = { 0 };
    set_destroy_callback(&fut->base, &cap);

    fixture_spin_to(&fixture, fixture.now + 1001);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_ERR_LIVENESS, cap.last_error);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);

    fixture_deinit(&fixture);
}

static void test_request_notify_timeout_with_remote_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_topic_t                              topic;
    request_future_t*                       fut = make_request_future_manual(&fixture, &topic, UINT64_C(0xCC02), 1000);
    request_future_remote_factory_context_t fac = { .cy = fixture.cy, .remote_id = UINT64_C(0xD001) };
    request_future_remote_t* const          remote = (request_future_remote_t*)cavl2_find_or_insert(
      &fut->remote_by_id, &fac.remote_id, request_future_remote_cavl_compare, &fac, request_future_remote_cavl_factory);
    TEST_ASSERT_NOT_NULL(remote);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(&fut->base, &cap);

    fixture_spin_to(&fixture, fixture.now + 1001);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_ERR_LIVENESS, cap.last_error);
    TEST_ASSERT_NOT_NULL(topic.request_futures_by_tag);

    fixture_spin_to(&fixture, fixture.now + (SESSION_LIFETIME / 2) + 1);
    TEST_ASSERT_NULL(topic.request_futures_by_tag);
    fixture_deinit(&fixture);
}

static void test_request_callback_set_after_done_immediate_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_publisher_t* const pub = cy_advertise_client(fixture.cy, cy_str("notify/request/immediate"), 16U);
    TEST_ASSERT_NOT_NULL(pub);
    cy_priority_set(pub, cy_prio_exceptional);
    const cy_us_t      req_deadline = fixture.now + 2000;
    const cy_bytes_t   msg          = { .size = 1U, .data = "K", .next = NULL };
    cy_future_t* const fut          = cy_request(pub, req_deadline, 4000, msg);
    TEST_ASSERT_NOT_NULL(fut);
    fixture_spin_to(&fixture, req_deadline + 1);
    TEST_ASSERT_TRUE(cy_future_done(fut));

    destroy_capture_t cap = { 0 };
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &cap;
    cy_future_context_set(fut, ctx);
    cy_future_callback_set(fut, destroy_on_notify);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);

    cy_unadvertise(pub);
    fixture_deinit(&fixture);
}

static void test_subscriber_notify_arrival_unordered_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_future_t* const sub = cy_subscribe(fixture.cy, cy_str("notify/sub/unordered"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    destroy_capture_t cap = { 0 };
    set_destroy_callback(sub, &cap);
    const cy_topic_t* const topic = cy_topic_find_by_name(fixture.cy, cy_str("notify/sub/unordered"));
    TEST_ASSERT_NOT_NULL(topic);
    dispatch_subscriber_message(&fixture, topic, UINT64_C(0xE001), header_msg_be, UINT64_C(1), 0x31U, fixture.now + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    fixture_spin_to(&fixture, fixture.now + 1);
    fixture_deinit(&fixture);
}

static void test_subscriber_notify_arrival_ordered_ejection_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_future_t* const sub = cy_subscribe_ordered(fixture.cy, cy_str("notify/sub/ordered"), 64U, 20);
    TEST_ASSERT_NOT_NULL(sub);
    destroy_capture_t cap = { 0 };
    set_destroy_callback(sub, &cap);
    const cy_topic_t* const topic = cy_topic_find_by_name(fixture.cy, cy_str("notify/sub/ordered"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_subscriber_message(
      &fixture, topic, UINT64_C(0xE002), header_msg_be, UINT64_C(100), 0x41U, fixture.now + 1);
    TEST_ASSERT_EQUAL_size_t(0U, cap.calls);

    fixture_spin_to(&fixture, fixture.now + 1000);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    fixture_spin_to(&fixture, fixture.now + 1);
    fixture_deinit(&fixture);
}

static void test_subscriber_notify_timeout_liveness_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_future_t* const sub = cy_subscribe(fixture.cy, cy_str("notify/sub/liveness"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    cy_subscriber_timeout_set(sub, 10);
    destroy_capture_t cap = { 0 };
    set_destroy_callback(sub, &cap);

    fixture_spin_to(&fixture, fixture.now + 20);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_ERR_LIVENESS, cap.last_error);
    fixture_spin_to(&fixture, fixture.now + 1);
    fixture_deinit(&fixture);
}

static void test_subscriber_notify_error_reordering_state_oom_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_future_t* const sub = cy_subscribe_ordered(fixture.cy, cy_str("notify/sub/oom_state"), 64U, 20);
    TEST_ASSERT_NOT_NULL(sub);
    destroy_capture_t cap = { 0 };
    set_destroy_callback(sub, &cap);
    fixture_fail_alloc_size(&fixture, sizeof(reordering_t), 1U);
    const cy_topic_t* const topic = cy_topic_find_by_name(fixture.cy, cy_str("notify/sub/oom_state"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_subscriber_message(
      &fixture, topic, UINT64_C(0xE003), header_msg_be, UINT64_C(101), 0x51U, fixture.now + 1);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_pending);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, cap.last_error);
    TEST_ASSERT_TRUE(fixture.async_error_count > 0U);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, fixture.last_async_error);

    fixture_spin_to(&fixture, fixture.now + 1);
    fixture_deinit(&fixture);
}

static void test_subscriber_notify_error_reordering_slot_oom_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_future_t* const sub = cy_subscribe_ordered(fixture.cy, cy_str("notify/sub/oom_slot"), 64U, 20);
    TEST_ASSERT_NOT_NULL(sub);
    destroy_capture_t cap = { 0 };
    set_destroy_callback(sub, &cap);
    fixture_fail_alloc_size(&fixture, sizeof(reordering_slot_t), 1U);
    const cy_topic_t* const topic = cy_topic_find_by_name(fixture.cy, cy_str("notify/sub/oom_slot"));
    TEST_ASSERT_NOT_NULL(topic);

    dispatch_subscriber_message(
      &fixture, topic, UINT64_C(0xE004), header_msg_be, UINT64_C(102), 0x61U, fixture.now + 1);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_pending);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, cap.last_error);
    TEST_ASSERT_TRUE(fixture.async_error_count > 0U);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEMORY, fixture.last_async_error);

    fixture_spin_to(&fixture, fixture.now + 1);
    fixture_deinit(&fixture);
}

static void test_subscriber_callback_set_after_done_immediate_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_future_t* const sub = cy_subscribe(fixture.cy, cy_str("notify/sub/immediate"), 64U);
    TEST_ASSERT_NOT_NULL(sub);
    const cy_topic_t* const topic = cy_topic_find_by_name(fixture.cy, cy_str("notify/sub/immediate"));
    TEST_ASSERT_NOT_NULL(topic);
    dispatch_subscriber_message(
      &fixture, topic, UINT64_C(0xE005), header_msg_be, UINT64_C(103), 0x71U, fixture.now + 1);
    TEST_ASSERT_TRUE(cy_future_done(sub));

    destroy_capture_t cap = { 0 };
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &cap;
    cy_future_context_set(sub, ctx);
    cy_future_callback_set(sub, destroy_on_notify);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);

    fixture_spin_to(&fixture, fixture.now + 1);
    fixture_deinit(&fixture);
}

static cy_breadcrumb_t make_breadcrumb(const fixture_t* const fixture,
                                       const uint64_t         remote_id,
                                       const cy_prio_t        prio,
                                       const uint64_t         topic_hash,
                                       const uint64_t         message_tag,
                                       const uint64_t         seqno)
{
    return (cy_breadcrumb_t){
        .cy          = fixture->cy,
        .priority    = prio,
        .remote_id   = remote_id,
        .topic_hash  = topic_hash,
        .message_tag = message_tag,
        .seqno       = seqno,
        .unicast_ctx = make_lane(remote_id, prio).ctx,
    };
}

static void test_respond_notify_ack_completion_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_breadcrumb_t breadcrumb =
      make_breadcrumb(&fixture, UINT64_C(0xF001), cy_prio_exceptional, UINT64_C(0x1111), UINT64_C(0x2222), 3U);
    const cy_bytes_t   msg = { .size = 1U, .data = "L", .next = NULL };
    cy_future_t* const fut = cy_respond_reliable(&breadcrumb, fixture.now + 100000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    dispatch_response_ack(&fixture,
                          UINT64_C(0xF001),
                          header_rsp_ack,
                          last_outgoing_rsp_tag(&fixture),
                          last_outgoing_rsp_seqno(&fixture),
                          last_outgoing_rsp_hash(&fixture),
                          last_outgoing_rsp_message_tag(&fixture),
                          fixture.now + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_OK, cap.last_error);
    fixture_deinit(&fixture);
}

static void test_respond_notify_nack_completion_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_breadcrumb_t breadcrumb =
      make_breadcrumb(&fixture, UINT64_C(0xF002), cy_prio_exceptional, UINT64_C(0x3333), UINT64_C(0x4444), 4U);
    const cy_bytes_t   msg = { .size = 1U, .data = "M", .next = NULL };
    cy_future_t* const fut = cy_respond_reliable(&breadcrumb, fixture.now + 100000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    dispatch_response_ack(&fixture,
                          UINT64_C(0xF002),
                          header_rsp_nack,
                          last_outgoing_rsp_tag(&fixture),
                          last_outgoing_rsp_seqno(&fixture),
                          last_outgoing_rsp_hash(&fixture),
                          last_outgoing_rsp_message_tag(&fixture),
                          fixture.now + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_ERR_NACK, cap.last_error);
    fixture_deinit(&fixture);
}

static void test_respond_notify_pending_media_error_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_breadcrumb_t breadcrumb =
      make_breadcrumb(&fixture, UINT64_C(0xF003), cy_prio_exceptional, UINT64_C(0x5555), UINT64_C(0x6666), 5U);
    const cy_bytes_t   msg = { .size = 1U, .data = "N", .next = NULL };
    cy_future_t* const fut = cy_respond_reliable(&breadcrumb, fixture.now + 120000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    fixture_fail_unicast_header(&fixture, header_rsp_rel, 1U, CY_ERR_MEDIA);
    fixture_spin_to(&fixture,
                    fixture.now + derive_ack_timeout(fixture.cy->ack_baseline_timeout, cy_prio_exceptional) + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_pending);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, cap.last_error);
    TEST_ASSERT_TRUE(fixture.async_error_count > 0U);
    TEST_ASSERT_EQUAL_INT(CY_ERR_MEDIA, fixture.last_async_error);
    fixture_deinit(&fixture);
}

static void test_respond_notify_pending_lag_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_breadcrumb_t breadcrumb =
      make_breadcrumb(&fixture, UINT64_C(0xF004), cy_prio_exceptional, UINT64_C(0x7777), UINT64_C(0x8888), 6U);
    const cy_bytes_t   msg      = { .size = 1U, .data = "O", .next = NULL };
    const cy_us_t      deadline = fixture.now + 120000;
    cy_future_t* const fut      = cy_respond_reliable(&breadcrumb, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    fixture_spin_to(&fixture, deadline - derive_ack_timeout(fixture.cy->ack_baseline_timeout, cy_prio_exceptional) + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_pending);
    TEST_ASSERT_EQUAL_INT(CY_ERR_LAG, cap.last_error);
    fixture_deinit(&fixture);
}

static void test_respond_notify_final_timeout_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_breadcrumb_t breadcrumb =
      make_breadcrumb(&fixture, UINT64_C(0xF005), cy_prio_exceptional, UINT64_C(0x9999), UINT64_C(0xAAAA), 7U);
    const cy_bytes_t   msg      = { .size = 1U, .data = "P", .next = NULL };
    const cy_us_t      deadline = fixture.now + 4000;
    cy_future_t* const fut      = cy_respond_reliable(&breadcrumb, deadline, msg);
    TEST_ASSERT_NOT_NULL(fut);

    destroy_capture_t cap = { 0 };
    set_destroy_callback(fut, &cap);
    fixture_spin_to(&fixture, deadline + 1);

    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    TEST_ASSERT_EQUAL_INT(CY_ERR_DELIVERY, cap.last_error);
    fixture_deinit(&fixture);
}

static void test_respond_callback_set_after_done_immediate_destroy(void)
{
    fixture_t fixture;
    fixture_init(&fixture);

    cy_breadcrumb_t breadcrumb =
      make_breadcrumb(&fixture, UINT64_C(0xF006), cy_prio_exceptional, UINT64_C(0xBBBB), UINT64_C(0xCCCC), 8U);
    const cy_bytes_t   msg = { .size = 1U, .data = "Q", .next = NULL };
    cy_future_t* const fut = cy_respond_reliable(&breadcrumb, fixture.now + 100000, msg);
    TEST_ASSERT_NOT_NULL(fut);

    dispatch_response_ack(&fixture,
                          UINT64_C(0xF006),
                          header_rsp_ack,
                          last_outgoing_rsp_tag(&fixture),
                          last_outgoing_rsp_seqno(&fixture),
                          last_outgoing_rsp_hash(&fixture),
                          last_outgoing_rsp_message_tag(&fixture),
                          fixture.now + 1);
    TEST_ASSERT_TRUE(cy_future_done(fut));

    destroy_capture_t cap = { 0 };
    cy_user_context_t ctx = CY_USER_CONTEXT_EMPTY;
    ctx.ptr[0]            = &cap;
    cy_future_context_set(fut, ctx);
    cy_future_callback_set(fut, destroy_on_notify);
    TEST_ASSERT_EQUAL_size_t(1U, cap.calls);
    TEST_ASSERT_TRUE(cap.saw_done);
    fixture_deinit(&fixture);
}

void setUp(void)
{
    TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count());
    cy_test_message_reset_counters();
}

void tearDown(void) { TEST_ASSERT_EQUAL_size_t(0U, cy_test_message_live_count()); }

int main(void)
{
    UNITY_BEGIN();
    RUN_TEST(test_publish_notify_ack_completion_destroy);
    RUN_TEST(test_publish_notify_timeout_completion_destroy);
    RUN_TEST(test_publish_notify_pending_media_error_destroy);
    RUN_TEST(test_publish_notify_pending_lag_destroy);
    RUN_TEST(test_publish_callback_set_after_done_immediate_destroy);
    RUN_TEST(test_request_notify_publish_pending_error_destroy);
    RUN_TEST(test_request_notify_publish_done_fatal_destroy);
    RUN_TEST(test_request_notify_on_response_best_effort_destroy);
    RUN_TEST(test_request_notify_on_response_reliable_destroy);
    RUN_TEST(test_request_notify_on_response_reliable_oom_destroy);
    RUN_TEST(test_request_notify_timeout_no_remote_destroy);
    RUN_TEST(test_request_notify_timeout_with_remote_destroy);
    RUN_TEST(test_request_callback_set_after_done_immediate_destroy);
    RUN_TEST(test_subscriber_notify_arrival_unordered_destroy);
    RUN_TEST(test_subscriber_notify_arrival_ordered_ejection_destroy);
    RUN_TEST(test_subscriber_notify_timeout_liveness_destroy);
    RUN_TEST(test_subscriber_notify_error_reordering_state_oom_destroy);
    RUN_TEST(test_subscriber_notify_error_reordering_slot_oom_destroy);
    RUN_TEST(test_subscriber_callback_set_after_done_immediate_destroy);
    RUN_TEST(test_respond_notify_ack_completion_destroy);
    RUN_TEST(test_respond_notify_nack_completion_destroy);
    RUN_TEST(test_respond_notify_pending_media_error_destroy);
    RUN_TEST(test_respond_notify_pending_lag_destroy);
    RUN_TEST(test_respond_notify_final_timeout_destroy);
    RUN_TEST(test_respond_callback_set_after_done_immediate_destroy);
    return UNITY_END();
}
