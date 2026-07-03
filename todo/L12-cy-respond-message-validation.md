# L12 — `cy_respond` does not validate its message argument

- **Severity:** 🟡 LOW (report L-12 / L-F5)
- **Confidence:** verified (code trace)
- **Subsystem:** core (`cy/cy.c`, RPC response)
- **Status:** OPEN

## Summary
`cy_publish`, `cy_publish_reliable`, `cy_request`, and `cy_respond_reliable` all reject a message with
`(data == NULL) && (size > 0)`. `cy_respond` does not — it forwards such a malformed `cy_bytes_t` straight to
`platform->vtable->unicast`, where a NULL-data / nonzero-size fragment violates the `cy_bytes_t` contract and will
typically crash in the platform's copy loop.

## Location
- `cy/cy.c:3930-3938` — `cy_respond` (no message validation).
- Compare: `cy/cy.c:2172-2173` (`do_publish`), `2409` (`cy_publish_reliable`), `2714-2715` (`cy_request`),
  `4055-4056` (`cy_respond_reliable`) — all validate.

## Fix direction
Add the same guard to `cy_respond`: reject with `CY_ERR_ARGUMENT` when `(message.data == NULL) && (message.size > 0)`.

## Regression test (required)
- Call `cy_respond` with `{ .size = 4, .data = NULL }`; assert it returns `CY_ERR_ARGUMENT` and does not invoke the
  platform unicast. Also assert a valid empty `{0, NULL}` response still sends. Must fail (forwarded/crash) on pre-fix
  code, pass after. Wire into `ctest`.

## Acceptance criteria
- [ ] `cy_respond` rejects NULL-data/nonzero-size messages with `CY_ERR_ARGUMENT`.
- [ ] Valid responses (including empty `{0, NULL}`) still send.
- [ ] Full suite green.

## Verification notes (adversarial cross-check)
- I will confirm the guard matches the sibling send APIs exactly (empty message with NULL data and size 0 stays valid)
  and that the platform unicast is not called on the rejected path.
