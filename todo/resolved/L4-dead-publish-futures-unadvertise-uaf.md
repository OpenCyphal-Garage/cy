# L4 — Dead `publish_futures` list; release-build UAF on `cy_unadvertise` with a live reliable future

- **Severity:** 🟡 LOW (contract-guarded; release-build UAF only on contract violation) (report L-4 / RP-F1)
- **Confidence:** verified (code trace)
- **Subsystem:** core (`cy/cy.c`, publisher lifecycle)
- **Status:** RESOLVED — fix direction (2): dead field/comment removed; explicit manual-cleanup contract kept.

## Resolution
Per maintainer directive, the abandoned auto-cancel design is removed rather than completed:
- Deleted the dead `cy_publisher_t::publish_futures` field and its `LIST_EMPTY` init (provably never
  populated or read).
- Deleted the incomplete `cy_unadvertise` debug scan (it could never detect request futures nor
  already-materialized publish futures, so it could not be made complete).
- Kept the existing `cy.h` contract as-is (it already requires destroying all publisher-created futures
  before unadvertising); a terse rationale comment in `cy.c` replaces the removed scan. Note the detection
  tradeoff: a forgotten *pending* future is still caught by the topic-level asserts in
  `topic_destroy`/`cy_destroy`, but now only at teardown, not at the offending `cy_unadvertise` call; and if
  a spin intervenes first, its timer UAFs the freed owner before teardown. An already-materialized-but-
  undestroyed publish future is a pure app-side leak that no assert catches — as was already the case, since
  the removed scan only inspected `pub_futures_by_tag`.
Regression coverage added in `tests/src/test_intrusive_future_notify_destroy.c`
(`test_publish_pending_future_destroy_then_unadvertise_clean`: destroy a pending reliable future →
unadvertise → spin past deadline → heaps clean, no stray retransmit, no UAF).
Note: the "must fail on pre-fix code" bar in the section below does not apply to this fix class — removing
provably-dead code and documenting the violation as UB has no failing-test signature, and the fault only
manifests on the (UB) contract-violation path, which cannot be safely exercised. The added test is instead a
contract-compliant-path leak/UAF guard (mutation-verified: dropping the payload `bytes_undup` makes it leak).

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
