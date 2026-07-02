# H6 — Responding to an anonymous v1.0 sender indexes a 128-element array at 255 (heap overflow)

- **Severity:** 🔴 HIGH (report H-6 / CAN-F2)
- **Confidence:** reproduced under ASan by the CAN agent; constants confirmed by orchestrator
- **Subsystem:** `cy_can/cy_can.c`
- **Status:** OPEN

## Summary
Anonymous Cyphal/CAN v1.0 frames arrive with source node-ID 255. If the application responds on the resulting
breadcrumb, `v_unicast_send` uses that 255 to index `unicast_tid[128]` — a 127-element out-of-bounds read+write past
the array (and past the `cy_can_t` object). Debug builds abort on an assert (DoS); NDEBUG builds corrupt the heap.

## Location
- `cy_can/cy_can.c:45` — `uint_least8_t unicast_tid[CANARD_NODE_ID_CAPACITY];` where `CANARD_NODE_ID_CAPACITY == 128`
  (`canard.h:64-65`: `CANARD_NODE_ID_MAX == 127`).
- `cy_can/cy_can.c:715-720` — `v_unicast_send`: `remote = lane->ctx.state[0]`; `assert(remote <= CANARD_NODE_ID_MAX)`;
  then `owner->unicast_tid[remote]` read-modify-write.
- `cy_can/cy_can.c:307` — `deliver()` stores `state[0] = source_node_id`; anonymous v1.0 frames carry
  `CANARD_NODE_ID_ANONYMOUS == 0xFF (255)`.

## Mechanism
An anonymous 13-bit v1.0 sender is delivered with `src = 255`; `deliver()` puts 255 into `lane.ctx.state[0]`. A
`cy_respond`/`cy_respond_reliable` on that breadcrumb calls `v_unicast_send` with `remote = 255`. `unicast_tid[255]`
is 127 bytes beyond the 128-byte array. The assert catches it only in debug; under NDEBUG the OOB access executes
before libcanard would reject the ID.

## Trigger / repro
A legacy anonymous v1.0 node publishes on a pinned subject the local node subscribes to, and the local application
calls `cy_respond*` on the received breadcrumb. Agent ASan repro: `heap-buffer-overflow in v_unicast_send`.

## Fix direction
Reject unroutable remotes at the top of `v_unicast_send` instead of asserting/indexing:
```c
if (remote > CANARD_NODE_ID_MAX) { return CY_ERR_ARGUMENT; }  // anonymous / invalid: cannot unicast
```
Consider also not exposing a "respondable" breadcrumb for anonymous senders (so the app can tell responses are
impossible), but the guard in `v_unicast_send` is the essential safety fix.

## Regression test (required)
- Add a test (in `cy_can/tests/`) that delivers an anonymous v1.0 frame (src 255) on a subscribed pinned topic and
  then calls `cy_respond` on the breadcrumb, asserting: returns `CY_ERR_ARGUMENT` (or a defined error), no OOB access,
  no assert-abort in debug. Must ASan-fail on pre-fix code.
- Wire into `ctest`; run the CAN unit target under ASan for this case.

## Acceptance criteria
- [ ] `v_unicast_send` never indexes `unicast_tid` with a value > `CANARD_NODE_ID_MAX`.
- [ ] Responding to an anonymous sender returns a defined error, no crash/assert, no heap access past the array.
- [ ] AddressSanitizer clean on the anonymous-respond path.
- [ ] Normal (node-ID ≤ 127) unicast/response still works; CAN suite green.

## Verification notes (adversarial cross-check)
- I will confirm the fix guards *before* the array access (not merely downgrading the assert), and that `remote` is
  the actual value derived from `lane.ctx.state[0]` on the anonymous path.
- I will test node-ID 127 (last valid) still works and 128/255 are rejected.
- I will check both `cy_respond` and `cy_respond_reliable` paths route through the guard.
- I will verify no other site indexes `unicast_tid` (or any per-node array) with an unchecked node-ID.
