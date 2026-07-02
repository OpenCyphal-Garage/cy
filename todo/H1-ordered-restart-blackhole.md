# H1 — Ordered subscription permanently blackholes a remote after it restarts (~50%)

- **Severity:** 🔴 HIGH (report H-1 / S-F1)
- **Confidence:** reproduced (repro test) + code trace
- **Subsystem:** core (`cy/cy.c`, reordering machinery)
- **Status:** RESOLVED

Resolved by making ordered reordering treat far-backward tag jumps as remote session restarts: old buffered messages
are force-ejected, the baseline is resequenced to the new tag, and late-drop recency is no longer refreshed.

## Summary
An ordered subscriber (`cy_subscribe_ordered`) linearizes each remote's wire tags against a baseline frozen at first
contact. When that remote reboots and re-seeds its random 64-bit tag counter, ~50% of the time the new tags
linearize into the "backward" half-space and are dropped as late stragglers — forever, because the wedged state
refreshes its own liveness before the drop check, so the staleness GC never rebuilds it.

## Location
- `cy/cy.c:3256-3257` — `reordering_push` sets `self->last_active_at = message.timestamp; enlist_head(...)` at the TOP,
  before any drop decision.
- `cy/cy.c:3277-3285` — backward/late drop: `if (lin_tag > INT64_MAX) return false;` (no state reset).
- `cy/cy.c:3231-3240` — `reordering_resequence` (the only recovery) is reachable only for large **forward** jumps.
- `cy/cy.c:3373-3383` — `reordering_drop_stale` keeps entries while `last_active_at + SESSION_LIFETIME >= now`.
- Contrast (correct, symmetric): `dedup_update` cy.c:3022-3027 resets on a large jump in **either** direction.

## Mechanism
`lin_tag = tag - tag_baseline`; `tag_baseline` frozen at first contact. After restart the remote's new baseline is a
fresh uniform random 64-bit value, so `P(lin_tag > INT64_MAX) = 0.5` → dropped at cy.c:3277. Because
`last_active_at` is refreshed at 3256 before the drop, a remote that keeps streaming keeps the wedged state fresh, so
`reordering_drop_stale` never fires and the correct baseline is never rebuilt. Self-heals only if the remote goes
silent > 60 s.

## Trigger / repro
Ordered subscriber on a topic; the publishing remote (stable `remote_id`, e.g. CAN node-id) reboots and continues
publishing within 60 s. ~50% of reboots wedge permanently.
- Reference case (borrow-source, NOT built): `TODO/repro-tests-reference.c :: test_ordered_subscription_blackholes_after_remote_restart`
  (delivered count frozen after the simulated restart).

## Compounding
For a **reliable + ordered** subscriber this couples with M8: post-restart message accepted by dedup, blackholed by
reordering, not acked → retransmit is a dedup duplicate → **false positive ACK** for every message. Fixing this
finding removes the systematic false-ACK case.

## Fix direction
Give reordering a bounded backward-straggler window, symmetric with dedup:
- Treat a `lin_tag` that is only *slightly* behind `last_ejected_lin_tag` (within a small bound) as a genuine late
  straggler → drop; but a `lin_tag` far in the backward half-space (indicative of a session restart / new random
  baseline) must trigger `reordering_resequence(self, tag)` and accept, mirroring the large-forward-jump path.
- **At minimum** (even if the window design is deferred): move the `last_active_at`/`enlist_head` recency refresh
  (cy.c:3256-3257) to *after* the LATE/BACKWARD drop checks, so a wedged state goes stale within 60 s and is rebuilt
  with a correct baseline on the next message. This bounds the outage to ≤ `SESSION_LIFETIME` instead of permanent.

## Regression test (required)
- Author the regression in the canonical test file (see Fix direction), borrowing & flipping the reference case `test_ordered_subscription_blackholes_after_remote_restart` from asserting the blackhole (delivered count
  frozen) to asserting **recovery**: after a restart with a backward-half-space baseline, the subscriber must deliver
  the post-restart messages (immediately if resequenced, or after ≤ `SESSION_LIFETIME` for the minimal fix).
- Add a companion test for a restart whose new baseline lands **forward** (must keep working) and one for a genuine
  **late straggler** (a truly old tag just behind the frontier — must still be dropped, ordering preserved).
- For the compounding case, add a **reliable + ordered** restart test asserting no false ACK is emitted after the fix
  (ties to M8). All wired into `ctest`; must fail on pre-fix code, pass after.

## Acceptance criteria
- [ ] After a simulated remote restart with a backward-half-space baseline, an ordered subscriber resumes delivering
      messages (either immediately via resequence, or within ≤ `SESSION_LIFETIME`), not never.
- [ ] `test_ordered_subscription_blackholes_after_remote_restart` is updated to assert recovery and passes.
- [ ] In-order, loss-free, non-restart streams are unaffected (no new drops; existing reordering tests green).
- [ ] The recency refresh no longer keeps a permanently-wedged state alive.
- [ ] Full suite green; `test_intrusive_reordering` still passes.

## Verification notes (adversarial cross-check)
- I will test **both** halves of the restart distribution: a new baseline that lands backward (the bug) and one that
  lands far-forward (already handled) — the fix must handle backward without breaking forward.
- I will test a genuine *late straggler* (a truly old tag arriving slightly after the frontier) still gets dropped —
  the fix must not turn every out-of-order-late message into a resequence (which would violate ordering).
- I will check the `reordering_eject` ordering assertion (`slot->lin_tag > last_ejected_lin_tag`) still holds after a
  backward-restart resequence.
- If only the minimal fix (move recency refresh) is taken, I will confirm the outage is actually bounded (state goes
  stale and rebuilds) and measure that the first post-recovery message is delivered.
- Combined with M8: I will run a reliable+ordered restart scenario and confirm no false ACKs after the fix.
