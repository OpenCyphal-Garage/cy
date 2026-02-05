/// Source: https://github.com/zubax/olga_scheduler
///
/// A single-file header-only EDF scheduler for embedded applications.
///
/// Copyright (c) Zubax Robotics  <info@zubax.com>
///
/// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated
/// documentation files (the "Software"), to deal in the Software without restriction, including without limitation
/// the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software,
/// and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
///
/// The above copyright notice and this permission notice shall be included in all copies or substantial portions of
/// the Software.
///
/// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
/// WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS
/// OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
/// OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#pragma once

#include <cavl2.h> // Add to your include paths: https://github.com/pavel-kirienko/cavl

#include <assert.h>
#include <stdint.h>

#ifdef __cplusplus
// This is, strictly speaking, useless because we do not define any functions with external linkage here,
// but it tells static analyzers that what follows should be interpreted as C code rather than C++.
extern "C"
{
#endif

typedef struct olga_t       olga_t;
typedef struct olga_event_t olga_event_t;

/// Represents a user-handled future event.
/// When the handler is invoked, the event is already removed from the scheduler.
/// If necessary, it can be re-inserted immediately from within the handler with a new deadline.
/// It is safe to destroy the event inside the handler.
/// The time units can be arbitrary.
struct olga_event_t
{
    CAVL2_T  base;
    int64_t  deadline;
    uint64_t seqno;
    void (*handler)(olga_t*, olga_event_t*, int64_t now);
    void* user;
};

// Convenience initializer for a fresh event (all fields zeroed, base pointers NULL).
#ifdef __cplusplus
#define OLGA_EVENT_INIT \
    olga_event_t {}
#else
#define OLGA_EVENT_INIT ((olga_event_t){ 0 })
#endif

/// The main scheduler type.
struct olga_t
{
    CAVL2_T* events;
    uint64_t next_seqno;     ///< Monotonic sequence number for FIFO ordering of equal-deadline events.
    int64_t (*now)(olga_t*); ///< Time provider; receives the scheduler to access user data if needed.
    void* user;
};

/// Current state assessment returned from olga_spin().
/// The `now` field contains the last sampled time from the user-provided clock, or INT64_MIN if not sampled.
typedef struct olga_spin_result_t
{
    int64_t next_deadline;
    int64_t worst_lateness;
    int64_t now;
} olga_spin_result_t;

/// To deinitialize, simply cancel all events; nothing else needs to be done.
/// The time units can be arbitrary.
static inline void olga_init(olga_t* const self, void* const user, int64_t (*const now)(olga_t* sched))
{
    assert(self != NULL);
    assert(now != NULL);
    self->events     = NULL;
    self->next_seqno = 0U;
    self->now        = now;
    self->user       = user;
}

// INTERNAL USE ONLY.
static inline CAVL2_RELATION olga_private_compare(const void* user, const CAVL2_T* event)
{
    const olga_event_t* const outer = (const olga_event_t*)user;
    const olga_event_t* const inner = (const olga_event_t*)event;
    if (outer->deadline != inner->deadline) {
        return (outer->deadline > inner->deadline) ? +1 : -1; // Later deadlines go to the right.
    }
    if (outer->seqno != inner->seqno) {
        return (outer->seqno > inner->seqno) ? +1 : -1; // Later insertion goes to the right.
    }
    return 0;
}

/// Schedule a one-time event.
/// The handler will be invoked at or asap after the deadline; the actual invocation time will be provided.
/// The scheduler pointer is passed to allow rescheduling from within the callback.
/// The event pointer provides access to the user data and deadline.
/// If the event is already scheduled, it will be automatically rescheduled with the new deadline.
/// The event must be either zero-initialized using OLGA_EVENT_INIT or have been used at least once.
/// Events are already canceled prior to handler invocation, so it is safe to re-register immediately from the handler.
/// The complexity is logarithmic in the number of pending events.
static inline void olga_defer(olga_t* const self,
                              const int64_t deadline,
                              void* const   user,
                              void (*const handler)(olga_t*, olga_event_t*, int64_t now),
                              olga_event_t* const out_event)
{
    assert(self != NULL);
    assert(handler != NULL);
    assert(out_event != NULL);
    (void)cavl2_remove_if(&self->events, &out_event->base);
    out_event->deadline = deadline;
    out_event->seqno    = self->next_seqno++;
    out_event->handler  = handler;
    out_event->user     = user;
    (void)cavl2_find_or_insert(&self->events, out_event, olga_private_compare, out_event, cavl2_trivial_factory);
}

/// No effect if the event has already been completed.
/// It is safe to cancel a freshly created event if it has been initialized with OLGA_EVENT_INIT.
/// The complexity is logarithmic in the number of pending events.
static inline void olga_cancel(olga_t* const self, olga_event_t* const event)
{
    assert(self != NULL);
    assert(event != NULL);
    (void)cavl2_remove_if(&self->events, &event->base);
    event->deadline = INT64_MIN;
}

/// True if the event is currently pending in the scheduler.
static inline bool olga_is_pending(const olga_t* const self, const olga_event_t* const event)
{
    assert(self != NULL);
    assert(event != NULL);
    return cavl2_is_inserted(self->events, &event->base);
}

/// Execute pending events strictly in the order of their deadlines until there are no pending events left.
/// Events with the same deadline are executed in the FIFO order.
/// The handler receives a freshly sampled `now` taken immediately before invocation.
/// This method should be invoked regularly to pump the event loop.
static inline olga_spin_result_t olga_spin(olga_t* const self)
{
    assert(self != NULL);
    olga_spin_result_t out = { .next_deadline = INT64_MAX, .worst_lateness = 0, .now = INT64_MIN };
    for (;;) { // GCOVR_EXCL_LINE
        olga_event_t* const event = (olga_event_t*)cavl2_min(self->events);
        if (event == NULL) {
            out.next_deadline = INT64_MAX;
            break;
        }
        const int64_t deadline = event->deadline;
        out.now                = self->now(self);
        if (out.now < deadline) {
            out.next_deadline = deadline;
            break;
        }
        cavl2_remove(&self->events, &event->base);
        event->handler(self, event, out.now);
        // event is no longer valid -- may be destroyed in the handler.

        const int64_t lateness = out.now - deadline; // Non-negative because now >= deadline.
        if (lateness > out.worst_lateness) {
            out.worst_lateness = lateness;
        }
    }
    return out;
}

#ifdef __cplusplus
}
#endif
