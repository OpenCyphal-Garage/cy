# L4 — Dead `publish_futures` list; release-build UAF on `cy_unadvertise` with a live reliable future

- **Severity:** 🟡 LOW (contract-guarded; release-build UAF only on contract violation) (report L-4 / RP-F1)
- **Confidence:** verified (code trace)
- **Subsystem:** core (`cy/cy.c`, publisher lifecycle)
- **Status:** OPEN

## Summary
`cy_publisher_t::publish_futures` is declared "for cancellation when the publisher is destroyed," initialized, and
never used — the intended auto-cancel-on-unadvertise was never implemented. So `cy_unadvertise` with a live
`cy_publish_reliable` future is caught only by a debug assert; in release the publisher is freed and the future's
`owner` dangles, so the next `publish_future_timeout` dereferences freed memory (UAF).

## Location
- `cy/cy.c:2079` — `cy_list_t publish_futures; // For cancellation when the publisher is destroyed.`
- `cy/cy.c:2101` — initialized to `LIST_EMPTY`, never appended to (`publish_future_t` has no list member).
- `cy/cy.c:2824-2829` — `cy_unadvertise` debug-only scan asserting `fut->owner != pub`.
- `cy/cy.c:2290, 2333` — `publish_future_timeout` derefs `self->owner->topic` / `->priority`.

## Fix direction
Pick one:
1. Implement the intended mechanism: enlist each `publish_future_t` on its publisher (add a `cy_list_member_t`), and
   in `cy_unadvertise` cancel/materialize all still-pending futures (materialize with a defined error). Makes
   unadvertise-with-live-futures safe.
2. Delete the dead field/comment and keep the documented hard precondition (app destroys futures first). Cheaper, but
   leaves the release-build UAF as "contract violation → UB."
Review recommends (1); at minimum do (2) so the half-built state doesn't mislead. Confirm choice with maintainer.

## Regression test (required)
- If (1): create a reliable publish future, `cy_unadvertise` without destroying it, spin past the deadline; assert no
  UAF (ASan-clean), the future materialized with a defined error, no leak. Test multiple live futures on one publisher.
- If (2): a test/assertion confirming the field is gone and the debug precondition assert fires under debug.
- Wire into `ctest`; must fail (ASan UAF, or missing detection) on pre-fix code, pass after.

## Acceptance criteria
- [ ] Either unadvertise-with-live-future is safe (future finalized, no UAF, no leak), or the dead field/comment is
      removed and the contract is explicit.
- [ ] No dangling `owner` deref reachable from `publish_future_timeout` after `cy_unadvertise`.
- [ ] Full suite green; ASan-clean on the exercised path.

## Verification notes (adversarial cross-check)
- If (1): I will ASan-verify unadvertise-then-spin, confirm the callback sees a defined error and can be destroyed;
  test several live futures.
- If (2): I will grep for any remaining `publish_futures` use and confirm the comment no longer promises a feature.
- I will confirm request futures are handled consistently (see L5).
