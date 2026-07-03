# M2 — Verbatim subscriber's extent starves a coexisting pattern subscriber's larger extent

- **Severity:** 🟠 MEDIUM (report M-2; found by 2 reviewers)
- **Confidence:** reproduced (repro test) + code trace
- **Subsystem:** core (`cy/cy.c`, subscription extent computation)
- **Status:** OPEN

## Summary
When a topic is matched by both a verbatim and a pattern subscriber, `subscription_extent_w_overhead` takes the
verbatim subscriber's extent and `break`s, discarding any larger pattern-subscriber extent. With grow-only readers,
if the verbatim couples first, the reader is never grown and the pattern subscriber's messages are silently truncated.

## Location
- `cy/cy.c:3535-3562` — `subscription_extent_w_overhead`; specifically `if (verbatim) { total = agg; break; }` at 3552-3554.
- Interacts with grow-only `reader_acquire`/`reader_grow_extent` (cy.c:890-924) and the refresh check in
  `wkv_cb_couple_new_subscription` (cy.c:3580-3587).

## Mechanism
The function should return the max extent across all couplings/subscribers (extent is a per-subscriber max-message
cap). Instead it overwrites the accumulator with the verbatim aggregate and stops. If the verbatim (small extent)
coupled first, the reader is created small; a later larger pattern subscriber does not grow it (the function now
returns the small value, not `> old`), so the pattern subscriber is truncated at steady state. Also causes a
non-monotonic shrink across a subject-ID reallocation.

## Trigger / repro
`cy_subscribe("ext/a", 16)` then `cy_subscribe("ext/*", 4096)` on the same node: reader extent stays 16+24.
- Reference case (borrow-source, NOT built): `TODO/repro-tests-reference.c :: test_pattern_extent_starved_by_verbatim`.

## Fix direction
Remove the `break` and the verbatim override; compute `total = larger(total, agg)` unconditionally across all
couplings so the reader extent is the maximum requested by any subscriber (verbatim or pattern).

## Regression test (required)
- Author the regression in the canonical test file (see Fix direction), borrowing & flipping the reference case `test_pattern_extent_starved_by_verbatim` to assert the reader extent grows to ≥ the largest subscriber's
  extent (pattern 4096 + HEADER_BYTES), regardless of coupling order (test both verbatim-first and pattern-first).
- Add a delivery test: a message larger than the verbatim extent but within the pattern extent is delivered
  untruncated to the pattern subscriber.
- Wire into `ctest`; must fail on pre-fix code, pass after.

## Acceptance criteria
- [ ] Reader extent = max over all couplings/subscribers on the topic, independent of coupling order.
- [ ] A pattern subscriber requesting a larger extent than a co-resident verbatim subscriber receives untruncated data.
- [ ] Extent does not shrink spuriously after a subject-ID reallocation (ties to L17).
- [ ] Full suite green.

## Verification notes (adversarial cross-check)
- I will test both orders and confirm the reader extent and actual delivered payload size for a mid-size message.
- I will confirm removing the `break` doesn't over-grow (extent should be the max, not the sum).
- I will check the interaction with L17 (reallocation): after a subject move the recomputed extent must still be the
  max, not a shrink.
- I will verify multiple pattern subscribers with differing extents all get the max.
