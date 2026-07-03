# M1 — Destroying a subscriber future requires an undocumented spin before `cy_destroy`

- **Severity:** 🟠 MEDIUM (report M-1; found by 3 reviewers)
- **Confidence:** reproduced (repro test) + code trace
- **Subsystem:** core (`cy/cy.c`, subscriber/teardown lifecycle)
- **Status:** RESOLVED

## Summary
`cy_future_destroy` on a subscriber only marks it disposed and arms a 0-deadline timer; the real teardown
(delisting from the root, root removal from the name/pattern indexes, coupling removal, freeing) runs on the next
spin. The documented sequence "destroy all user objects, then `cy_destroy`" therefore asserts in debug and leaks in
release (destroying topics that still carry live couplings).

## Location
- `cy/cy.c:2909-2923` — `subscriber_dispose` sets `disposed`, `future_deadline_arm(base, 0)`; no synchronous free.
- `cy/cy.c:2896-2907` — `subscriber_timeout` runs `subscriber_destroy` only when the deferred event fires.
- `cy/cy.c:4446-4448` — `cy_destroy` asserts `wkv_is_empty(&cy->subscribers_by_name)` / `_by_pattern`.
- `cy/cy.c:4139`, `cy/cy.c:4468-4476` — `topic_destroy` / `cy_destroy` assert `couplings == NULL` / `is_implicit`.

## Mechanism
Publishers free synchronously in `cy_unadvertise`; subscribers defer. If the app destroys its last subscriber and
immediately calls `cy_destroy` (no intervening `cy_spin_*`), the root is still registered → debug assert; release
proceeds to destroy topics with live couplings, leaking subscriber/root/couplings/reordering states + message
payloads.

## Trigger / repro
`sub = cy_subscribe(...); ...; cy_future_destroy(sub); cy_destroy(cy);` with no spin between.
- Reference case (borrow-source, NOT built): `TODO/repro-tests-reference.c :: test_subscriber_destroy_requires_spin_before_cy_destroy`
  (root still registered until a spin runs).

## Fix direction
Prefer draining deferred destructions inside `cy_destroy` before its emptiness asserts: iterate
`subscribers_by_name` roots and run `subscriber_destroy` on each `disposed` subscriber (asserting none are
non-disposed, since the contract still requires the app to have destroyed them). This makes the documented sequence
correct with no new app obligation. (Alternative, weaker: document that one `cy_spin_once()` is required after
destroying the last subscriber — but code-side draining is preferable and matches how zombie request futures are
already reaped in `topic_destroy`.)

## Regression test (required)
- Author the regression in the canonical test file (see Fix direction), borrowing & flipping the reference case `test_subscriber_destroy_requires_spin_before_cy_destroy` to assert `cy_destroy` immediately after destroying
  all subscribers (no spin) completes cleanly: no assert (debug), no leak (guarded-heap balanced), all roots/topics
  freed.
- Add a variant with a pattern subscriber + coupled implicit topic to exercise coupling teardown in the drain path.
- Wire into `ctest`; must fail (assert/leak) on pre-fix code, pass after.

## Acceptance criteria
- [ ] `cy_destroy` immediately after destroying all subscribers is clean in both debug and release (no assert, no leak).
- [ ] Deferred subscriber teardown still works normally when a spin does occur (no double-free).
- [ ] Existing lifecycle tests (e.g. destroy-after-unsubscribe-and-spin) still pass.
- [ ] Full suite + guarded-heap balance green.

## Verification notes (adversarial cross-check)
- I will run destroy-then-`cy_destroy`-no-spin under the guarded heap and assert zero residual fragments/bytes and
  zero live messages.
- I will confirm the drain path does not double-free when the app *did* spin first (both orders clean).
- I will check a disposed subscriber with interned reordering slots and coupled topics is fully torn down by the drain.
- I will verify the drain doesn't fire user callbacks re-entrantly during `cy_destroy` (silenced teardown).
