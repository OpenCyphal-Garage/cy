//                            ____                   ______            __          __
//                           / __ `____  ___  ____  / ____/_  ______  / /_  ____  / /
//                          / / / / __ `/ _ `/ __ `/ /   / / / / __ `/ __ `/ __ `/ /
//                         / /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ / / / / /_/ / /
//                         `____/ .___/`___/_/ /_/`____/`__, / .___/_/ /_/`__,_/_/
//                             /_/                     /____/_/
//
// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#include "cy_can.h"
#include <cy_platform.h>
#include <canard.h>

#define RAPIDHASH_COMPACT
#include <rapidhash.h>

#include <assert.h>
#include <string.h>

#if __STDC_VERSION__ < 201112L
#define static_assert(x, ...) typedef char _sa_gl(_sa_, __LINE__)[(x) ? 1 : -1]
#define _sa_gl(a, b)          _sa_gl2(a, b)
#define _sa_gl2(a, b)         a##b
#endif

/// The Cy session-layer header is fixed at 24 bytes. Must agree with cy.c.
#define HEADER_BYTES 24U

/// Service-ID reserved for v1.1 unicast transfers over Cyphal/CAN.
#define UNICAST_SERVICE_ID 511U

/// Default extent for incoming unicast messages; will grow as needed.
#define UNICAST_EXTENT_INITIAL (HEADER_BYTES + 1024U)

typedef struct subject_writer_t        subject_writer_t;
typedef struct subject_reader_t        subject_reader_t;
typedef struct subject_reader_pinned_t subject_reader_pinned_t;

// =====================================================================================================================

typedef struct
{
    cy_platform_t          base; // Must be first (upcast pattern).
    const cy_can_vtable_t* vtable;
    void*                  user;
    uint_least8_t          iface_count;
    uint64_t               prng_state;

    canard_t canard;

    canard_subscription_t unicast_sub; // Service-ID 511 for unicast.

    // Per-remote unicast transfer-ID counters (one per possible CAN node-ID).
    uint_least8_t unicast_tid[CANARD_NODE_ID_CAPACITY];

    subject_reader_t* tombstone_head; // Deferred destruction list to avoid reentrancy issues.

    size_t   subject_writer_count;
    size_t   subject_reader_count;
    uint64_t v10_rx_count;
    uint64_t v11_rx_count;
    uint64_t oom_count; // cy_can-level OOM (message wrapper allocation failures, etc.).
} cy_can_t;

struct subject_writer_t
{
    cy_subject_writer_t base;
    uint_least8_t       next_tid_13b;
    uint_least8_t       next_tid_16b;
};

struct subject_reader_t
{
    cy_subject_reader_t   base;
    canard_subscription_t sub_16b;
    cy_can_t*             owner;
    subject_reader_t*     next_tombstone;
};

// The runtime type is determined as pinned=subject_id<=CY_SUBJECT_ID_PINNED_MAX.
struct subject_reader_pinned_t
{
    subject_reader_t      base;
    canard_subscription_t sub_13b;
    uint64_t              phony_tag;
    uint_least8_t         phony_header[HEADER_BYTES]; // Precomputed for 13-bit reception.
};

static subject_reader_pinned_t* as_pinned(subject_reader_t* const self)
{
    return (self->base.subject_id <= CY_SUBJECT_ID_PINNED_MAX) ? (subject_reader_pinned_t*)self : NULL;
}

// =====================================================================================================================
// MEMORY BRIDGE

static void* can_mem_alloc(const canard_mem_t mem, const size_t size)
{
    cy_can_t* const self = (cy_can_t*)mem.context;
    return self->vtable->realloc(self->user, NULL, size);
}

static void can_mem_free(const canard_mem_t mem, const size_t size, void* const ptr)
{
    cy_can_t* const self = (cy_can_t*)mem.context;
    (void)size;
    if (ptr != NULL) {
        self->vtable->realloc(self->user, ptr, 0);
    }
}

static const canard_mem_vtable_t can_mem_vtable = { .free = can_mem_free, .alloc = can_mem_alloc };

static canard_mem_t make_mem(cy_can_t* const self)
{
    return (canard_mem_t){ .vtable = &can_mem_vtable, .context = self };
}

static canard_mem_set_t make_mem_set(cy_can_t* const self)
{
    const canard_mem_t m = make_mem(self);
    return (canard_mem_set_t){ .tx_transfer = m, .tx_frame = m, .rx_session = m, .rx_payload = m, .rx_filters = m };
}

// =====================================================================================================================
// SERIALIZATION HELPERS (little-endian, must match cy.c)

static void le_serialize_u32(uint_least8_t* const ptr, const uint32_t value)
{
    for (size_t i = 0; i < 4; i++) {
        ptr[i] = (uint_least8_t)((value >> (i * 8U)) & 0xFFU);
    }
}

static void le_serialize_u64(uint_least8_t* const ptr, const uint64_t value)
{
    for (size_t i = 0; i < 8; i++) {
        ptr[i] = (uint_least8_t)((value >> (i * 8U)) & 0xFFU);
    }
}

/// Portable decimal conversion for subject-ID -> topic name hash. Buffer must be at least 11 bytes.
static size_t uint_to_decimal(uint32_t value, char* const buf)
{
    char   tmp[11];
    size_t len = 0;
    do {
        tmp[len++] = (char)('0' + (char)(value % 10U));
        value /= 10U;
    } while (value > 0);
    for (size_t i = 0; i < len; i++) {
        buf[i] = tmp[len - 1U - i];
    }
    return len;
}

// =====================================================================================================================
// MESSAGE BUFFER
//
// The logical message is seg0[] (flex array, inline data) concatenated with seg1 (optional external data),
// with `skip` bytes removed from the front.
//
//  - 16-bit single-frame:  seg0 = [payload copy],         seg1 = NULL.   origin = NULL.
//  - 16-bit multi-frame:   seg0 = [] (empty),             seg1 = view.   origin = canard buffer.
//  - 13-bit single-frame:  seg0 = [phony hdr + payload],  seg1 = NULL.   origin = NULL.
//  - 13-bit multi-frame:   seg0 = [phony hdr],            seg1 = view.   origin = canard buffer.

typedef struct
{
    cy_message_t  base;
    cy_can_t*     owner;
    void*         origin; // Multi-frame payload buffer from canard (NULL for single-frame). Freed on destroy.
    const void*   seg1;   // Second segment: points into origin (NULL if single-segment).
    size_t        seg1_len;
    size_t        seg0_len; // Length of inline data in seg0[].
    size_t        skip;
    uint_least8_t seg0[]; // Flex array: inline data (phony header and/or single-frame payload).
} can_message_t;

static void v_message_skip(cy_message_t* const base, const size_t offset)
{
    can_message_t* const self  = (can_message_t*)base;
    const size_t         total = self->seg0_len + self->seg1_len;
    const size_t         avail = (total > self->skip) ? (total - self->skip) : 0;
    self->skip += (offset < avail) ? offset : avail;
}

static size_t v_message_read(const cy_message_t* const base, const size_t offset, const size_t size, void* const dest)
{
    const can_message_t* const self  = (const can_message_t*)base;
    const size_t               total = self->seg0_len + self->seg1_len;
    const size_t               start = self->skip + offset;
    if (start >= total) {
        return 0;
    }
    const size_t avail   = total - start;
    const size_t to_read = (size < avail) ? size : avail;
    size_t       done    = 0;
    size_t       pos     = start;
    char*        out     = (char*)dest;
    if (pos < self->seg0_len) {
        const size_t rem = self->seg0_len - pos;
        const size_t n   = ((to_read - done) < rem) ? (to_read - done) : rem;
        (void)memcpy(out, self->seg0 + pos, n);
        done += n;
        out += n;
        pos += n;
    }
    if ((done < to_read) && (self->seg1 != NULL)) {
        const size_t n = to_read - done;
        (void)memcpy(out, (const char*)self->seg1 + (pos - self->seg0_len), n);
        done += n;
    }
    return done;
}

static size_t v_message_size(const cy_message_t* const base)
{
    const can_message_t* const self  = (const can_message_t*)base;
    const size_t               total = self->seg0_len + self->seg1_len;
    return (total > self->skip) ? (total - self->skip) : 0;
}

static void v_message_destroy(cy_message_t* const base)
{
    can_message_t* const self = (can_message_t*)base;
    if (self->origin != NULL) {
        self->owner->vtable->realloc(self->owner->user, self->origin, 0);
    }
    self->owner->vtable->realloc(self->owner->user, self, 0);
}

static const cy_message_vtable_t message_vtable = { .skip    = v_message_skip,
                                                    .read    = v_message_read,
                                                    .size    = v_message_size,
                                                    .destroy = v_message_destroy };

/// Allocate a can_message_t with `inline_extra` bytes for the flex array seg0[].
static can_message_t* make_message(cy_can_t* const owner, const size_t inline_extra)
{
    can_message_t* const msg =
      (can_message_t*)owner->vtable->realloc(owner->user, NULL, sizeof(can_message_t) + inline_extra);
    if (msg != NULL) {
        (void)memset(msg, 0, sizeof(*msg));
        msg->base  = CY_MESSAGE_INIT(&message_vtable);
        msg->owner = owner;
    }
    return msg;
}

// =====================================================================================================================
// cy_bytes_t -> canard_bytes_chain_t ALIASING

static canard_bytes_chain_t cy_bytes_to_canard(const cy_bytes_t message)
{
    static_assert(offsetof(canard_bytes_chain_t, bytes.size) == offsetof(cy_bytes_t, size), "");
    static_assert(offsetof(canard_bytes_chain_t, bytes.data) == offsetof(cy_bytes_t, data), "");
    static_assert(offsetof(canard_bytes_chain_t, next) == offsetof(cy_bytes_t, next), "");
    return (canard_bytes_chain_t){ .bytes = { .size = message.size, .data = message.data },
                                   .next  = (const canard_bytes_chain_t*)message.next };
}

// =====================================================================================================================
// CANARD VTABLE CALLBACKS

static canard_us_t v_canard_now(const canard_t* const self)
{
    const cy_can_t* const owner = (const cy_can_t*)self->user_context;
    return owner->vtable->now(owner->user);
}

static bool v_canard_tx(canard_t* const      self,
                        void* const          user_context,
                        const canard_us_t    deadline,
                        const uint_least8_t  iface_index,
                        const bool           fd,
                        const uint32_t       extended_can_id,
                        const canard_bytes_t can_data)
{
    cy_can_t* const     owner = (cy_can_t*)self->user_context;
    const uint_least8_t len   = (uint_least8_t)can_data.size;
    (void)user_context;
    (void)deadline;
    assert(iface_index < owner->iface_count);
    if (fd && (owner->vtable->tx_fd != NULL)) {
        return owner->vtable->tx_fd(owner->user, iface_index, extended_can_id, can_data.data, len);
    }
    return owner->vtable->tx_classic(owner->user, iface_index, extended_can_id, can_data.data, len);
}

static const canard_vtable_t canard_vtbl = { .now = v_canard_now, .tx = v_canard_tx, .filter = NULL };

// =====================================================================================================================
// SUBSCRIPTION CALLBACKS

static void deliver(cy_can_t* const       owner,
                    const uint32_t* const subject_id,
                    const uint_least8_t   source_node_id,
                    const canard_prio_t   priority,
                    const canard_us_t     timestamp,
                    can_message_t* const  msg)
{
    cy_lane_t lane;
    (void)memset(&lane, 0, sizeof(lane));
    lane.id                   = source_node_id;
    lane.prio                 = (cy_prio_t)priority;
    lane.ctx.state[0]         = (unsigned char)source_node_id;
    const cy_message_ts_t mts = { .timestamp = timestamp, .content = &msg->base };
    cy_on_message(&owner->base, lane, subject_id, mts);
}

/// 16-bit subscription callback. Payload already contains the Cy session header.
static void v_on_msg_16b(canard_subscription_t* const self,
                         const canard_us_t            timestamp,
                         const canard_prio_t          priority,
                         const uint_least8_t          source_node_id,
                         const uint_least8_t          transfer_id,
                         const canard_payload_t       payload)
{
    (void)transfer_id;
    subject_reader_t* const reader     = (subject_reader_t*)self->user_context;
    cy_can_t* const         owner      = reader->owner;
    const bool              multiframe = (payload.origin.data != NULL);
    owner->v11_rx_count++;

    can_message_t* const msg = make_message(owner, multiframe ? 0 : payload.view.size);
    if (msg == NULL) {
        if (multiframe) {
            owner->vtable->realloc(owner->user, payload.origin.data, 0);
        }
        owner->oom_count++;
        return;
    }
    if (multiframe) {
        msg->seg1     = payload.view.data;
        msg->seg1_len = payload.view.size;
        msg->origin   = payload.origin.data;
    } else {
        (void)memcpy(msg->seg0, payload.view.data, payload.view.size);
        msg->seg0_len = payload.view.size;
    }
    const uint32_t sid = reader->base.subject_id;
    deliver(owner, &sid, source_node_id, priority, timestamp, msg);
}

/// 13-bit subscription callback. Must prepend a precomputed phony Cy session header.
static void v_on_msg_13b(canard_subscription_t* const self,
                         const canard_us_t            timestamp,
                         const canard_prio_t          priority,
                         const uint_least8_t          source_node_id,
                         const uint_least8_t          transfer_id,
                         const canard_payload_t       payload)
{
    (void)transfer_id;
    subject_reader_pinned_t* const pinned     = (subject_reader_pinned_t*)self->user_context;
    cy_can_t* const                owner      = pinned->base.owner;
    const bool                     multiframe = (payload.origin.data != NULL);
    owner->v10_rx_count++;

    const size_t         inline_size = HEADER_BYTES + (multiframe ? 0 : payload.view.size);
    can_message_t* const msg         = make_message(owner, inline_size);
    if (msg == NULL) {
        if (multiframe) {
            owner->vtable->realloc(owner->user, payload.origin.data, 0);
        }
        owner->oom_count++;
        return;
    }
    // Stamp precomputed phony header with incrementing tag.
    pinned->phony_tag++;
    (void)memcpy(msg->seg0, pinned->phony_header, HEADER_BYTES);
    le_serialize_u64(msg->seg0 + 16, pinned->phony_tag);
    msg->seg0_len = HEADER_BYTES;

    if (multiframe) {
        msg->seg1     = payload.view.data;
        msg->seg1_len = payload.view.size;
        msg->origin   = payload.origin.data;
    } else {
        if (payload.view.size > 0) {
            (void)memcpy(msg->seg0 + HEADER_BYTES, payload.view.data, payload.view.size);
        }
        msg->seg0_len += payload.view.size;
    }
    const uint32_t sid = pinned->base.base.subject_id;
    deliver(owner, &sid, source_node_id, priority, timestamp, msg);
}

/// Service-ID 511 subscription callback for unicast transfers.
static void v_on_msg_unicast(canard_subscription_t* const self,
                             const canard_us_t            timestamp,
                             const canard_prio_t          priority,
                             const uint_least8_t          source_node_id,
                             const uint_least8_t          transfer_id,
                             const canard_payload_t       payload)
{
    (void)transfer_id;
    cy_can_t* const owner      = (cy_can_t*)self->user_context;
    const bool      multiframe = (payload.origin.data != NULL);

    can_message_t* const msg = make_message(owner, multiframe ? 0 : payload.view.size);
    if (msg == NULL) {
        if (multiframe) {
            owner->vtable->realloc(owner->user, payload.origin.data, 0);
        }
        owner->oom_count++;
        return;
    }
    if (multiframe) {
        msg->seg1     = payload.view.data;
        msg->seg1_len = payload.view.size;
        msg->origin   = payload.origin.data;
    } else {
        (void)memcpy(msg->seg0, payload.view.data, payload.view.size);
        msg->seg0_len = payload.view.size;
    }
    deliver(owner, NULL, source_node_id, priority, timestamp, msg);
}

static const canard_subscription_vtable_t sub_vtable_16b     = { .on_message = v_on_msg_16b };
static const canard_subscription_vtable_t sub_vtable_13b     = { .on_message = v_on_msg_13b };
static const canard_subscription_vtable_t sub_vtable_unicast = { .on_message = v_on_msg_unicast };

// =====================================================================================================================
// SUBJECT WRITER

static cy_subject_writer_t* v_subject_writer_new(cy_platform_t* const base, const uint32_t subject_id)
{
    cy_can_t* const         owner = (cy_can_t*)base;
    subject_writer_t* const self  = (subject_writer_t*)owner->vtable->realloc(owner->user, NULL, sizeof(*self));
    if (self != NULL) {
        (void)memset(self, 0, sizeof(*self));
        self->base.subject_id = subject_id;
        owner->subject_writer_count++;
    }
    CY_TRACE(owner->base.cy, "CAN writer S%08jx n=%zu", (uintmax_t)subject_id, owner->subject_writer_count);
    return (cy_subject_writer_t*)self;
}

static void v_subject_writer_destroy(cy_platform_t* const platform, cy_subject_writer_t* const base)
{
    cy_can_t* const         owner = (cy_can_t*)platform;
    subject_writer_t* const self  = (subject_writer_t*)base;
    assert(owner->subject_writer_count > 0);
    owner->subject_writer_count--;
    owner->vtable->realloc(owner->user, self, 0);
}

static cy_err_t v_subject_writer_send(cy_platform_t* const       platform,
                                      cy_subject_writer_t* const base,
                                      const cy_us_t              deadline,
                                      const cy_prio_t            priority,
                                      const cy_bytes_t           message)
{
    cy_can_t* const         owner = (cy_can_t*)platform;
    subject_writer_t* const self  = (subject_writer_t*)base;
    const uint32_t          sid   = base->subject_id;
    const uint_least8_t     ibm   = (uint_least8_t)((1U << owner->iface_count) - 1U);

    assert((message.data != NULL) && (message.size >= HEADER_BYTES));
    const bool     pinned      = (sid <= CY_SUBJECT_ID_PINNED_MAX);
    const bool     best_effort = (((const uint_least8_t*)message.data)[0] == 0); // header_msg_be
    const uint64_t e_oom       = owner->canard.err.oom;
    const uint64_t e_cap       = owner->canard.err.tx_capacity;

    bool ok;
    if (pinned && best_effort) { // V1.0 PATH: 13-bit subject-ID, strip the 24-byte Cy header.
        cy_bytes_t stripped = message;
        stripped.data       = (const char*)stripped.data + HEADER_BYTES;
        stripped.size -= HEADER_BYTES;
        if ((stripped.size == 0) && (stripped.next != NULL)) {
            stripped = *stripped.next;
        }
        ok = canard_publish_13b(&owner->canard,
                                deadline,
                                ibm,
                                (canard_prio_t)priority,
                                (uint16_t)sid,
                                self->next_tid_13b++,
                                cy_bytes_to_canard(stripped),
                                NULL);
    } else { // V1.1 PATH: 16-bit subject-ID, full message including Cy header.
        ok = canard_publish_16b(&owner->canard,
                                deadline,
                                ibm,
                                (canard_prio_t)priority,
                                (uint16_t)sid,
                                self->next_tid_16b++,
                                cy_bytes_to_canard(message),
                                NULL);
    }
    if (ok) {
        return CY_OK;
    }
    if (owner->canard.err.oom > e_oom) {
        return CY_ERR_MEMORY;
    }
    if (owner->canard.err.tx_capacity > e_cap) {
        return CY_ERR_CAPACITY;
    }
    return CY_ERR_ARGUMENT;
}

// =====================================================================================================================
// SUBJECT READER

static void build_phony_header(subject_reader_pinned_t* const self, const uint32_t subject_id)
{
    (void)memset(self->phony_header, 0, HEADER_BYTES);
    self->phony_header[3] = 0xFFU; // lage = -1 (int8_t)
    le_serialize_u32(&self->phony_header[4], (uint32_t)(UINT32_MAX - subject_id));
    char         decimal[11];
    const size_t dlen = uint_to_decimal(subject_id, decimal);
    le_serialize_u64(&self->phony_header[8], rapidhash(decimal, dlen));
}

/// Finalize a reader: unsubscribe from canard and free memory. Does NOT unlink from any list.
static void reader_finalize(cy_can_t* const owner, subject_reader_t* const self)
{
    canard_unsubscribe(&owner->canard, &self->sub_16b);
    subject_reader_pinned_t* const pinned = as_pinned(self);
    if (pinned != NULL) {
        canard_unsubscribe(&owner->canard, &pinned->sub_13b);
    }
    assert(owner->subject_reader_count > 0);
    owner->subject_reader_count--;
    owner->vtable->realloc(owner->user, self, 0);
}

static cy_subject_reader_t* v_subject_reader_new(cy_platform_t* const base,
                                                 const uint32_t       subject_id,
                                                 const size_t         extent)
{
    cy_can_t* const         owner  = (cy_can_t*)base;
    const bool              pinned = (subject_id <= CY_SUBJECT_ID_PINNED_MAX);
    const size_t            sz     = pinned ? sizeof(subject_reader_pinned_t) : sizeof(subject_reader_t);
    subject_reader_t* const self   = (subject_reader_t*)owner->vtable->realloc(owner->user, NULL, sz);
    if (self == NULL) {
        return NULL;
    }
    (void)memset(self, 0, sz);
    self->base.subject_id = subject_id;
    self->base.extent     = extent;
    self->owner           = owner;

    // The extent from Cy already includes the header overhead.
    const bool ok_16b = canard_subscribe_16b(&owner->canard,
                                             &self->sub_16b,
                                             (uint16_t)subject_id,
                                             extent,
                                             CANARD_DEFAULT_TRANSFER_ID_TIMEOUT_us,
                                             &sub_vtable_16b);
    assert(ok_16b);
    (void)ok_16b;
    self->sub_16b.user_context = self;

    if (pinned) {
        subject_reader_pinned_t* const p = (subject_reader_pinned_t*)self;
        // 13-bit payload does not include the Cy header; we prepend it ourselves.
        const size_t extent_13b = (extent > HEADER_BYTES) ? (extent - HEADER_BYTES) : 0;
        const bool   ok_13b     = canard_subscribe_13b(&owner->canard,
                                                 &p->sub_13b,
                                                 (uint16_t)subject_id,
                                                 extent_13b,
                                                 CANARD_DEFAULT_TRANSFER_ID_TIMEOUT_us,
                                                 &sub_vtable_13b);
        assert(ok_13b);
        (void)ok_13b;
        p->sub_13b.user_context = p;
        build_phony_header(p, subject_id);
    }

    owner->subject_reader_count++;
    CY_TRACE(owner->base.cy, "CAN reader S%08jx extent=%zu pinned=%d", (uintmax_t)subject_id, extent, (int)pinned);
    return (cy_subject_reader_t*)self;
}

/// Tombstone a reader: unlink from main list, add to tombstone list for deferred finalization.
static void v_subject_reader_destroy(cy_platform_t* const platform, cy_subject_reader_t* const base)
{
    cy_can_t* const         owner = (cy_can_t*)platform;
    subject_reader_t* const self  = (subject_reader_t*)base;
    self->next_tombstone          = owner->tombstone_head;
    owner->tombstone_head         = self;
}

static void v_subject_reader_extent_set(cy_platform_t* const       base,
                                        cy_subject_reader_t* const reader_base,
                                        const size_t               extent)
{
    (void)base;
    subject_reader_t* const self          = (subject_reader_t*)reader_base;
    self->sub_16b.extent                  = extent;
    subject_reader_pinned_t* const pinned = as_pinned(self);
    if (pinned != NULL) {
        pinned->sub_13b.extent = (extent > HEADER_BYTES) ? (extent - HEADER_BYTES) : 0;
    }
}

// =====================================================================================================================
// UNICAST

static cy_err_t v_unicast_send(cy_platform_t* const   base,
                               const cy_lane_t* const lane,
                               const cy_us_t          deadline,
                               const cy_bytes_t       message)
{
    cy_can_t* const     owner  = (cy_can_t*)base;
    const uint_least8_t remote = lane->ctx.state[0];
    assert(remote <= CANARD_NODE_ID_MAX);
    const uint64_t      e_oom  = owner->canard.err.oom;
    const uint64_t      e_cap  = owner->canard.err.tx_capacity;
    const uint_least8_t tid    = owner->unicast_tid[remote];
    owner->unicast_tid[remote] = (uint_least8_t)((tid + 1U) % CANARD_TRANSFER_ID_MODULO);
    const bool ok              = canard_request(&owner->canard,
                                   deadline,
                                   (canard_prio_t)lane->prio,
                                   UNICAST_SERVICE_ID,
                                   remote,
                                   tid,
                                   cy_bytes_to_canard(message),
                                   NULL);
    if (ok) {
        return CY_OK;
    }
    if (owner->canard.err.oom > e_oom) {
        return CY_ERR_MEMORY;
    }
    if (owner->canard.err.tx_capacity > e_cap) {
        return CY_ERR_CAPACITY;
    }
    return CY_ERR_ARGUMENT;
}

static void v_unicast_extent_set(cy_platform_t* const base, const size_t extent)
{
    cy_can_t* const owner = (cy_can_t*)base;
    if (extent > owner->unicast_sub.extent) {
        owner->unicast_sub.extent = extent;
    }
}

// =====================================================================================================================
// EVENT LOOP

static cy_err_t v_spin(cy_platform_t* const base, const cy_us_t deadline)
{
    cy_can_t* const     owner = (cy_can_t*)base;
    const uint_least8_t ibm   = (uint_least8_t)((1U << owner->iface_count) - 1U);
    cy_us_t             now   = owner->vtable->now(owner->user);

    while (now < deadline) {
        canard_poll(&owner->canard, ibm);

        // O(1) tombstone cleanup: finalize all deferred reader destructions.
        while (owner->tombstone_head != NULL) {
            subject_reader_t* const rd = owner->tombstone_head;
            owner->tombstone_head      = rd->next_tombstone;
            reader_finalize(owner, rd);
        }

        cy_can_frame_t frame;
        (void)memset(&frame, 0, sizeof(frame));
        if (owner->vtable->rx(owner->user, &frame, deadline)) {
            now                           = owner->vtable->now(owner->user);
            const canard_bytes_t can_data = { .size = frame.len, .data = frame.data };
            (void)canard_ingest_frame(&owner->canard, now, frame.iface_index, frame.can_id, can_data);
        }
        now = owner->vtable->now(owner->user);
    }
    canard_poll(&owner->canard, ibm);
    return CY_OK;
}

// =====================================================================================================================
// MISC

static cy_us_t v_now(cy_platform_t* const base)
{
    const cy_can_t* const owner = (const cy_can_t*)base;
    return owner->vtable->now(owner->user);
}

static void* v_realloc(cy_platform_t* const base, void* const ptr, const size_t new_size)
{
    const cy_can_t* const owner = (const cy_can_t*)base;
    return owner->vtable->realloc(owner->user, ptr, new_size);
}

static uint64_t v_random(cy_platform_t* const base)
{
    cy_can_t* const owner = (cy_can_t*)base;
    return owner->vtable->random(owner->user);
}

static const cy_platform_vtable_t platform_vtable = {
    .subject_writer_new        = v_subject_writer_new,
    .subject_writer_destroy    = v_subject_writer_destroy,
    .subject_writer_send       = v_subject_writer_send,
    .subject_reader_new        = v_subject_reader_new,
    .subject_reader_destroy    = v_subject_reader_destroy,
    .subject_reader_extent_set = v_subject_reader_extent_set,
    .unicast                   = v_unicast_send,
    .unicast_extent_set        = v_unicast_extent_set,
    .spin                      = v_spin,
    .now                       = v_now,
    .realloc                   = v_realloc,
    .random                    = v_random,
};

// =====================================================================================================================
// PUBLIC API

cy_platform_t* cy_can_new(const uint_least8_t          iface_count,
                          const size_t                 tx_queue_capacity,
                          const cy_can_vtable_t* const vtable,
                          void* const                  user)
{
    if ((vtable == NULL) || (vtable->tx_classic == NULL) || (vtable->rx == NULL) || (vtable->now == NULL) ||
        (vtable->realloc == NULL) || (vtable->random == NULL) || (iface_count == 0) ||
        (iface_count > CANARD_IFACE_COUNT)) {
        return NULL;
    }
    cy_can_t* const self = (cy_can_t*)vtable->realloc(user, NULL, sizeof(cy_can_t));
    if (self == NULL) {
        return NULL;
    }
    (void)memset(self, 0, sizeof(*self));
    self->vtable      = vtable;
    self->user        = user;
    self->iface_count = iface_count;
    self->prng_state  = vtable->random(user);

    self->base.subject_id_modulus = CY_SUBJECT_ID_MODULUS_16bit;
    self->base.vtable             = &platform_vtable;

    const bool ok = canard_new(&self->canard, &canard_vtbl, make_mem_set(self), tx_queue_capacity, self->prng_state, 0);
    if (!ok) {
        vtable->realloc(user, self, 0);
        return NULL;
    }
    self->canard.tx.fd        = (vtable->tx_fd != NULL);
    self->canard.user_context = self;

    const bool ok_uni = canard_subscribe_request(&self->canard,
                                                 &self->unicast_sub,
                                                 UNICAST_SERVICE_ID,
                                                 UNICAST_EXTENT_INITIAL,
                                                 CANARD_DEFAULT_TRANSFER_ID_TIMEOUT_us,
                                                 &sub_vtable_unicast);
    if (!ok_uni) {
        canard_destroy(&self->canard);
        vtable->realloc(user, self, 0);
        return NULL;
    }
    self->unicast_sub.user_context = self;
    return &self->base;
}

cy_can_stats_t cy_can_stats(const cy_platform_t* const base)
{
    const cy_can_t* const owner = (const cy_can_t*)base;
    return (cy_can_stats_t){
        .subject_writer_count     = owner->subject_writer_count,
        .subject_reader_count     = owner->subject_reader_count,
        .v10_rx_count             = owner->v10_rx_count,
        .v11_rx_count             = owner->v11_rx_count,
        .oom_count                = owner->oom_count,
        .canard_err_oom           = owner->canard.err.oom,
        .canard_err_tx_capacity   = owner->canard.err.tx_capacity,
        .canard_err_tx_sacrifice  = owner->canard.err.tx_sacrifice,
        .canard_err_tx_expiration = owner->canard.err.tx_expiration,
        .canard_err_rx_frame      = owner->canard.err.rx_frame,
        .canard_err_rx_transfer   = owner->canard.err.rx_transfer,
        .canard_err_collision     = owner->canard.err.collision,
    };
}

void* cy_can_user(const cy_platform_t* const base)
{
    const cy_can_t* const owner = (const cy_can_t*)base;
    return owner->user;
}

void cy_can_destroy(cy_platform_t* const base)
{
    cy_can_t* const owner = (cy_can_t*)base;
    while (owner->tombstone_head != NULL) {
        subject_reader_t* const rd = owner->tombstone_head;
        owner->tombstone_head      = rd->next_tombstone;
        reader_finalize(owner, rd);
    }
    canard_unsubscribe(&owner->canard, &owner->unicast_sub);
    canard_destroy(&owner->canard);
    owner->vtable->realloc(owner->user, owner, 0);
}
