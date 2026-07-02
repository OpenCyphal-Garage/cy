# L13 — `cy_new` leaks the remap table if broadcast reader/writer creation fails

- **Severity:** 🟡 LOW (OOM-path leak) (report L-13 / L-F4)
- **Confidence:** verified (code trace)
- **Subsystem:** core (`cy/cy.c`, construction)
- **Status:** OPEN

## Summary
After `remap_parse` populates the remap wkv, if `subject_reader_new`/`subject_writer_new` for the broadcast subject
fails, `cy_new` unwinds with a bare `mem_free(cy, cy)` that skips the remap drain `cy_destroy` performs — leaking all
remap wkv nodes and their heap-copied `to` strings.

## Location
- `cy/cy.c:4409-4425` — broadcast reader/writer failure branches (`mem_free(cy, cy)` only).
- `cy/cy.c:4482-4487` — the remap drain in `cy_destroy` that these branches skip.
- `cy/cy.c:4384` — where `remap_parse` populates `cy->remap`.

## Fix direction
Call `cy_destroy(cy)` in those two failure branches instead of the bare `mem_free`. `cy_destroy` already handles this
half-built state safely (NULL broadcast handles guarded, olga empty, indexes empty, remap drained, `platform->cy`
unlinked) — verified during review.

## Regression test (required)
- OOM-injection test: force `subject_reader_new` (then separately `subject_writer_new`) to fail during `cy_new` with a
  non-empty remap string; assert the guarded heap is fully balanced afterward (no leaked remap nodes / `to` strings)
  and `platform->cy == NULL`. Must fail (leak) on pre-fix code, pass after.
- Wire into `ctest` (extend `test_intrusive_misc` or a construction test with the fail-after allocator seam).

## Acceptance criteria
- [ ] Both broadcast-setup failure branches free the remap table (no leak); guarded-heap balanced.
- [ ] `platform->cy` cleared on these failure paths.
- [ ] `cy_destroy` on the half-built instance remains safe (no double-free / NULL deref).
- [ ] Full suite green.

## Verification notes (adversarial cross-check)
- I will inject OOM at the reader and at the writer step (both branches) with a non-empty remap and confirm zero
  residual fragments/bytes, and that `cy_destroy` on the half-built instance doesn't touch uninitialized fields.
