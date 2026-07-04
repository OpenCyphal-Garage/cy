# M2 — Verbatim subscriber's extent starves a coexisting pattern subscriber's larger extent

- **Severity:** 🟠 MEDIUM (report M-2; found by 2 reviewers)
- **Confidence:** reproduced (repro test) + code trace
- **Subsystem:** core (`cy/cy.c`, subscription extent computation)
- **Status:** RESOLVED

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

## Resolution
`subscription_extent_w_overhead()` now computes the maximum `extent_pure` across every subscriber in every coupling
and adds `HEADER_BYTES` once. The fix is covered by:
- `test_subscription_extent_uses_pattern_max_after_verbatim_first`.
- `test_subscription_extent_reallocate_keeps_pattern_max_after_verbatim`.
- `test_subscription_extent_delivery_not_truncated_by_verbatim`.

Pre-fix targeted intrusive tests failed on the three M2 regressions. After the fix, targeted intrusive tests passed for
x64/x32 and C99/C11, and the full Debug suite passed with static analysis enabled.
