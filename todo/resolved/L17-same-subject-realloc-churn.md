# L17 — Same-subject reallocation transiently destroys and recreates the platform reader/writer

- **Severity:** 🟡 LOW (report L-17 / CRDT-F14, L-F weaker)
- **Confidence:** verified (code trace)
- **Subsystem:** core (`cy/cy.c`, `topic_allocate` victory branch)
- **Status:** RESOLVED

## Summary
When a topic's probe sequence cycles back to its *current* subject-ID (possible because `subject_id(hash, e)` is
non-injective in `e`), the victory branch releases its own reader/writer before re-acquiring the same subject. If the
refcount hits zero the platform handle is destroyed and immediately recreated — needless transport churn (e.g. IGMP
leave/join, transfer-ID state loss) and a failure window if the re-acquire OOMs.

## Location
- `cy/cy.c:1462-1495` — the victory branch releases old reader/writer then `topic_sync_subject_reader` re-acquires.
- Contrast: the *displacement* case deliberately acquires-before-release to preserve the handle; the same-subject case
  does not short-circuit.

## Fix direction
Short-circuit the victory branch when `new_sid == old_sid` and the topic already holds the handles: skip the
release/re-acquire entirely (keep the existing reader/writer, just update `evictions` and re-index). Preserve the
allocation semantics and the diagnostics (`diag_topic_reallocated`) — a same-subject "reallocation" with unchanged
subject-ID should not tear down transport state.

## Regression test (required)
- Add a test that drives an eviction change which maps a topic back to its **same** subject-ID (construct hashes so
  `subject_id(h, e) == subject_id(h, e')` for the transition), with an active subscriber (so a reader exists), and
  assert the platform reader handle is **not** destroyed/recreated (e.g. via the subject-tracker or a
  destroy-count hook) across the reallocation. Must fail (handle recreated) on pre-fix code, pass after.
- Wire into `ctest` (extend `test_intrusive_topic_allocation`).

## Acceptance criteria
- [x] A reallocation that keeps the same subject-ID does not destroy/recreate the platform reader/writer.
- [x] Allocation results and diagnostics are otherwise unchanged (CRDT equivalence preserved).
- [x] No refcount imbalance or OOM window introduced.
- [x] Full suite, incl. `test_intrusive_topic_allocation` / `_exhaustive`, green.

## Verification notes (adversarial cross-check)
- I will confirm the handle survives via the subject-tracker (no destroy event) for a same-subject reallocation, and
  that a genuine subject *change* still transitions correctly (acquire-before-release preserved for displacement).
- I will confirm reader/writer refcounts stay balanced and pinned-topic re-pin behaviour is unaffected.
- I will re-run the exhaustive allocation test to confirm converged outcomes are unchanged.
