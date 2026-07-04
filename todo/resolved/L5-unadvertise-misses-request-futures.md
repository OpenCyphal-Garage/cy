# L5 — `cy_unadvertise` does not check live request futures

- **Severity:** 🟡 LOW (contract-guarded; diagnosability gap) (report L-5 / C-F4)
- **Confidence:** verified (code trace)
- **Subsystem:** core (`cy/cy.c`, publisher/request lifecycle)
- **Status:** RESOLVED — by override: incomplete detector removed, no per-publisher assertion added.

## Resolution
The suggested fix (add a debug assertion over `request_futures_by_tag` in `cy_unadvertise`) is
intentionally **overridden** by maintainer directive. A request future keys on its topic, not on a
specific publisher, and a topic may host several publishers, so a live request future cannot be
attributed back to the `pub` being unadvertised — the early per-publisher check is infeasible.
Instead the whole incomplete `cy_unadvertise` scan is removed (see L4). Detection instead happens later,
at teardown rather than at the offending call: `topic_destroy` asserts every `request_futures_by_tag`
entry is `finalized` (`cy/cy.c`), which fires if the application forgot to destroy a live request future. The `cy.h` contract on
`cy_unadvertise` already requires destroying all publisher-created futures first (which covers request
futures), so no wording change was needed.
Regression coverage added in `tests/src/test_intrusive_future_notify_destroy.c`
(`test_request_zombie_reaped_by_cy_destroy_after_unadvertise`: request future acks a reliable response →
destroyed into a zombie → unadvertise → `cy_destroy` while the zombie is still pending → the
`topic_destroy` zombie loop reaps it, heaps clean, no UAF).
Note: like L4, the "must fail on pre-fix code" bar below is not applicable — this fix removes an incomplete
detector rather than a behavior. The test instead guards the retained library-owned cleanup on the
contract-compliant path (mutation-verified: deleting the `topic_destroy` zombie loop makes it leak two fragments).

## Summary
`cy_unadvertise`'s debug scan only inspects `pub_futures_by_tag`. A live `cy_request` future, once its inner publish
sub-future completes, sits only in `topic->request_futures_by_tag` and is never checked. The topic survives (implicit
timeout); its eventual reaping asserts `future->finalized` (debug) or `request_future_destroy`s a live future
(release UAF) — arbitrarily later and far from the offending `cy_unadvertise`.

## Location
- `cy/cy.c:2824-2829` — unadvertise debug scan (covers only `pub_futures_by_tag`).
- `cy/cy.c:4180-4184` — `topic_destroy` asserts `future->finalized` per `request_futures_by_tag` entry.
- `cy/cy.c:2549-2557` — `request_publish_callback` destroys the publish sub-future once delivery completes, after
  which the request future no longer carries `owner == pub`.

## Fix direction
In `cy_unadvertise`, when `pub_count` reaches 0, add a debug assertion that every entry in
`topic->request_futures_by_tag` is finalized (zero live publishers ⇒ no legitimately-live request future can remain).
Surfaces the contract violation at the offending call instead of 600 s later. (The hard release-UAF fix is the same
class as L4 — cancellation-on-teardown; the minimal ask here is the early detection.)

## Regression test (required)
- Debug test: create a request future, let its delivery phase complete (inner publish destroyed), then `cy_unadvertise`
  without destroying the request future; assert the new early assertion fires. Assert it does NOT fire when the app
  destroys the request future first.
- Wire into `ctest`.

## Acceptance criteria
- [ ] `cy_unadvertise` detects a leftover live request future at the point of the violation (debug).
- [ ] No false positive when the app destroys request futures before unadvertising.
- [ ] Full suite green.

## Verification notes (adversarial cross-check)
- I will confirm the assertion covers the post-delivery state (inner publish already gone) — the window the existing
  check misses — and that zombie (finalized) request futures do not trip it.
