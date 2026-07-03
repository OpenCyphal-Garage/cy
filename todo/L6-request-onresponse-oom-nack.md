# L6 — `request_on_response` OOM answers NACK (kills the stream) and finalizes the request with `CY_ERR_MEMORY`

- **Severity:** 🟡 LOW (report L-6 / C-F2)
- **Confidence:** verified (code trace)
- **Subsystem:** core (`cy/cy.c`, RPC response path)
- **Status:** OPEN

## Summary
If allocating the per-remote dedup state fails on the first reliable response, `request_on_response` returns false →
`cy_on_message` sends a NACK. Per the documented semantics a NACK means "client no longer interested," so a streaming
server tears down the stream — a transient local OOM masquerades as deliberate closure. It also disarms and marks the
request future done with `CY_ERR_MEMORY`. This contradicts the message-path OOM policy, which deliberately does **not**
NACK ("the remote will retransmit and we might accept it then").

## Location
- `cy/cy.c:2604-2610` — OOM path returns false + disarms + notifies with `CY_ERR_MEMORY`.
- `cy/cy.c:4900-4902` — `cy_on_message` sends `header_rsp_nack` when `ack == false` for a reliable response.
- Contrast: `cy/cy.c:3455-3459` (message path: OOM → no nack, let sender retransmit); `model/DESIGN.md:169`.

## Fix direction
On OOM, send **nothing** (neither ack nor nack) so the responder's backoff retransmits and a later attempt can
succeed — mirroring the message-path policy. Give `request_on_response` a tri-state result (ack / nack / silent);
have `cy_on_message` suppress `send_response_ack` on silent. Do not permanently finalize the request future on a
transient OOM (drop the disarm; keep the diagnostic `ON_ASYNC_ERROR`).

## Regression test (required)
- Reliable response arrives, per-remote state allocation forced to OOM once; assert no NACK is sent and the request
  future is not permanently finalized with `CY_ERR_MEMORY`; then allow the retransmit to succeed and assert delivery.
  Must fail on pre-fix code (NACK / future killed), pass after.
- Wire into `ctest` (extend `test_intrusive_rpc`).

## Acceptance criteria
- [ ] A transient OOM on a first reliable response results in silence (no NACK), allowing retransmission.
- [ ] The request future is not permanently finalized by a transient OOM.
- [ ] A genuine "client gone" still produces a NACK (real-case semantics preserved).
- [ ] Full suite + `test_intrusive_rpc` green.

## Verification notes (adversarial cross-check)
- I will confirm the tri-state is wired end-to-end (OOM → silent → no `send_response_ack`), that the genuine
  destroyed-future (zombie) path still NACKs new seqnos, and that OOM-then-success leaves no state corruption/leak.
