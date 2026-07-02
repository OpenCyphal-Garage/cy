# L5 — `cy_unadvertise` does not check live request futures

- **Severity:** 🟡 LOW (contract-guarded; diagnosability gap) (report L-5 / C-F4)
- **Confidence:** verified (code trace)
- **Subsystem:** core (`cy/cy.c`, publisher/request lifecycle)
- **Status:** OPEN

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
