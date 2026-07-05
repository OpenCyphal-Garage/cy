# M8 — False positive ACK for a reliable message no subscriber accepted

- **Severity:** 🟠 MEDIUM standalone; 🔴 HIGH when compounded with H1 (report M-8 / S-F2)
- **Confidence:** reproduced (repro test) + code trace
- **Subsystem:** core (`cy/cy.c`, subscriber data path)
- **Status:** RESOLVED (2026-07-04)

## Resolution
Split the dedup primitive into `dedup_touch` (recency/enlist, always) + `dedup_check` (read-only duplicate test) +
`dedup_commit` (bitmap mutation), and deferred the commit in `on_message` to the tail, gated on `reliable &&
acknowledge` — so a message no subscriber accepted is never recorded, and its retransmit is re-attempted (or, for a
window-late ordered drop, correctly resolves the publisher future with `CY_ERR_DELIVERY`) instead of being
false-ACKed. Closed the reordering self-disposal vector by driving `acknowledge` from delivery: `subscriber_notify`
returns false when the subscriber was already disposed, and `reordering_push` refuses the current message via a
single `sub->disposed` guard after its forced-eject sites (covers both the capacity-overflow and far-backward-restart
ejections). Chosen public semantics: window-dropped reliable+ordered messages report `CY_ERR_DELIVERY` (cy.h docs
intentionally kept high-level; E2E reordering/migration tests updated). Regression suite:
`tests/src/test_intrusive_false_ack.c` (10 tests) — the false-ack and late-retransmit vector tests fail pre-fix and
pass post-fix; the rest are behavior-preservation guards that pass both — plus
`test_intrusive_dedup.c`/`test_intrusive_topic_allocation.c` updated for the API split. Full suite green under static
analysis across x64/x32 × c99/c11.

## Summary
`on_message` marks a reliable message's tag as received in the dedup filter **before** any subscriber accepts it. If
acceptance fails for all subscribers on the first delivery, no ack is sent (correct) and the sender retransmits — but
the retransmission is now a dedup "duplicate" and is **positively acknowledged** though the application never received
the message. The sender records success for a lost message.

## Location
- `cy/cy.c:3467` — `dedup_update(...)` marks the tag seen, before the subscriber loop (3476-3529).
- `cy/cy.c:3469` — duplicate path returns `true` (→ ACK) before touching any subscriber.
- `cy/cy.c:4838-4839` — ACK is sent when `on_message` returned true.
- Failure-to-accept paths: reordering slot OOM `cy.c:3324-3335` (returns false), reordering state OOM `cy.c:3518-3521`,
  all-subscribers-disposed skip `cy.c:3482-3486`.
- In-code comment acknowledging only the narrow disposed case: `cy.c:3462-3466`.
- Reordering self-disposal vector (a distinct instance of this class): `reordering_drop_stale(sub, …)` at `cy.c:3488`
  can eject a stale interned message whose delivery callback destroys its own subscriber (deferred → `sub->disposed`
  becomes true but `sub` stays valid); the code then still runs `reordering_push` and sets `acknowledge = true`
  (`cy.c:3504-3517`) for the current message, which `subscriber_notify` will drop because the sub is disposed
  (`cy.c:2947`) → false ACK. **Widened by the C1 fix** (`resolved/C1-cavl-factory-uaf.md`, now RESOLVED): the stale sweep
  used to run inside `reordering_cavl_factory` only on a cache-miss; it now runs on **every** ordered receive, so this
  trigger is far more reachable than before. It requires a stale reordering state that still holds interned slots
  (i.e. a poll-starved window), so it is narrow, but no longer cache-miss-gated.

## Mechanism
Dedup state mutation precedes the acceptance decision. First delivery: acceptance fails for everyone → `acknowledge`
stays false → no ACK (good). Retransmit: `dedup_update` returns "duplicate" → `on_message` returns true → ACK sent,
subscribers never invoked → false success.

## Trigger / repro
Reliable publisher → subscriber under memory pressure (reordering alloc fails first attempt), or a subscriber
disposed within the one-poll-cycle window a retransmit arrives.
- Reference case (borrow-source, NOT built): `TODO/repro-tests-reference.c :: test_reliable_false_ack_after_failed_acceptance`.

## Compounding (why it can be HIGH)
With H1 on a reliable + ordered subscriber whose remote restarted, dedup accepts, reordering blackholes, and every
retransmit false-ACKs — systematic, not just an OOM edge. Fixing H1 removes the systematic case; this fix removes
the standalone OOM / disposed-subscriber cases.

## Fix direction
Split "consult" from "commit": only record the tag as received once at least one subscriber has actually accepted it.
- Introduce `dedup_check(dedup, tag)` (already exists) for the up-front duplicate test, and defer the state-mutating
  `dedup_update`/commit until after the subscriber loop reports `acknowledge == true`. On a genuine first-delivery
  total failure, leave the dedup state unchanged so the retransmit retries real delivery.
- Preserve the genuine-duplicate fast path: a tag already committed must still be recognized and ACKed without
  re-delivery.
- **Gap to close:** deferring `dedup_update` only fixes the *dedup/retransmit* half. The reordering self-disposal
  vector above sets `acknowledge` directly from `reordering_push`, so it must be handled separately — e.g. re-check
  `sub->disposed` after `reordering_drop_stale`/before `acknowledge = true`, or drive `acknowledge` from
  actual delivery rather than from acceptance. Do not rely on the C1 change to cover it.

## Regression test (required)
- Author the regression in the canonical test file (see Fix direction), borrowing & flipping the reference case `test_reliable_false_ack_after_failed_acceptance` to assert the *fixed* behaviour: after a first-delivery
  acceptance failure (OOM), the retransmit is **delivered** to the application (arrival count increments) and only
  then ACKed — no ACK for an undelivered message.
- Add a genuine-duplicate test: a truly re-received (already-delivered) reliable message is still ACKed without
  double-delivery.
- Wire into `ctest`; must fail on pre-fix code, pass after.

## Acceptance criteria
- [x] A reliable message that no subscriber accepted on first delivery is not recorded as received; its retransmit is
      delivered (or re-attempted), not silently ACKed.
- [x] Genuine duplicates are still deduplicated and ACKed without re-delivery (no regression to dedup).
- [x] Best-effort path and non-OOM normal path unchanged.
- [x] Full suite + `test_intrusive_dedup` green.

## Verification notes (adversarial cross-check)
- I will exercise all three non-acceptance triggers (slot OOM, state OOM, all-disposed) and confirm the retransmit is
  delivered rather than false-ACKed.
- I will confirm the commit-after-accept change does not break at-most-once for genuine duplicates (no double
  delivery) and does not leak dedup state on the failure path.
- I will run the compounded reliable+ordered restart scenario (with H1 fixed) and confirm zero false ACKs.
- I will check multi-subscriber partial acceptance: if any subscriber accepts, commit+ACK; if none, no commit.
