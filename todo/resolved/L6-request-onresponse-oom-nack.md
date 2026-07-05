# L6 - `request_on_response` OOM answers NACK (resolved)

Resolved by making reliable response reception tri-state internally: ACK, NACK, or silent.

On per-remote dedup-state OOM, Cy now emits `CY_ERR_MEMORY` via async diagnostics but sends no response ACK/NACK and
leaves the request future pending/armed, allowing responder retransmission to succeed later. Real client-gone cases
still NACK: missing/destroyed request futures and finalized zombie futures rejecting unseen seqnos.

Regression coverage:

- Direct `request_on_response()` OOM remains pending/silent.
- Wire-level OOM sends no ACK/NACK, then retransmit succeeds with `header_rsp_ack`.
- Destroyed request future before first reliable response still emits `header_rsp_nack`.
