# H3 — The documented auto-destroy idiom cancels reliable delivery on the first transient error

- **Severity:** 🔴 HIGH (report H-3 / RPC C-F1)
- **Confidence:** reproduced (repro test) + code trace
- **Subsystem:** core (`cy/cy.c`) + docs (`cy.h`, `README.md`, `examples/`)
- **Status:** RESOLVED

Resolved by removing the unsafe recommendation and documenting a local one-shot helper callback that checks
`cy_future_done()` before calling `cy_future_destroy()`. Pending progress/error callbacks remain visible, but the
documented helper ignores them so reliable delivery continues until completion.

## Summary
The old docs recommended `cy_future_callback_set(future, cy_future_destroy)` as a fire-and-forget idiom. But the
reliable-delivery timeout handlers invoke the callback while the future is still **pending** on every transient send
failure or scheduler-lag event. With auto-destroy installed, that first transient notification destroys the pending
future — which cancels the operation. Retransmissions stop after one failed attempt, precisely under the congestion
reliable delivery exists to survive.

## Location
- Recommendation: `cy.h:171`, `README.md:159` ("Will destroy itself when done"), `examples/example_file_server.c` (~76-79).
- Notify-while-pending on transient error: `cy/cy.c:2362-2365` (`publish_future_timeout`), `cy/cy.c:4005-4009`
  (`respond_future_timeout`).
- Cancellation semantics: `cy/cy.c:2368-2373` (`publish_future_dispose` materializes/cancels a not-done future).
- Correct internal precedent: `cy/cy.c:2549-2556` (`request_publish_callback` guards with `cy_future_done`).

## Mechanism
On a transient send error (`CY_ERR_CAPACITY`/`CY_ERR_MEDIA`) or lag detection, the timeout handler calls
`future_notify` although `done == false`. The public idiom's callback is `cy_future_destroy`, which does not check
`done`, so it disposes a pending future → cancels retransmission, frees the payload, removes the index entry. The
library's own code already knows the guard is needed (it uses `cy_future_done` before destroying the inner publish
future), but the app-facing idiom omits it.

## Trigger / repro
`cy_publish_reliable` (or `cy_respond_reliable`) + `cy_future_callback_set(f, cy_future_destroy)`, then a single
transient send failure on a retransmission (e.g. TX queue momentarily full).
- Reference case (borrow-source, NOT built): `TODO/repro-tests-reference.c :: test_auto_destroy_idiom_cancels_reliable_delivery_on_transient_error`
  (control ≥4 sends over the budget; with one injected transient failure exactly 2 sends then abandoned).

## Resolution
No new library API or callback semantics were added. The resolution is documentation-only plus demo hygiene:
- Stop recommending `cy_future_destroy` directly as a generic fire-and-forget callback.
- Document a local one-shot helper callback that checks `cy_future_done()` before destroying.
- Keep transient-error/progress callbacks visible to applications.
- Update demos so they do not use the unsafe direct-destroy callback pattern.

## Acceptance criteria
- [x] The documented fire-and-forget teardown no longer cancels a pending reliable operation on a transient error.
- [x] Transient errors are still observable to an application that wants them.
- [x] `cy.h`, `README.md`, and the example are updated to the safe idiom and are internally consistent.
- [x] No new public API is added for this use case.

## Verification notes (adversarial cross-check)
- I will drive both a transient send failure and a scheduler-lag event and confirm the future survives to keep
  retrying under the recommended idiom.
- I will confirm the fix does not leak on the normal completion path (guarded destroy still fires on done).
- I will check `cy_respond_reliable` (not just `cy_publish_reliable`) is covered, since it has the same pattern.
- I will grep docs/examples for any remaining unguarded `cy_future_callback_set(*, cy_future_destroy)` recommendation.
- I will confirm the README's adjacent warning ("do not destroy unwanted futures right away — that cancels the
  operation") is now consistent with the recommended idiom.
