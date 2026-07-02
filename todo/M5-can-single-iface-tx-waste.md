# M5 — CAN single-interface configuration wastes TX-queue capacity on every unicast/service transfer

- **Severity:** 🟠 MEDIUM → low-medium (report M-5 / CAN-F3)
- **Confidence:** verified (code trace); "leak" corrected to transient waste by triage
- **Subsystem:** `cy_can/cy_can.c` (+ libcanard service-transfer API)
- **Status:** OPEN — ⚠️ **REQUIRES UPSTREAM libcanard COORDINATION** (per maintainer 2026-07-02)

> **Upstream dependency.** The clean fix (option 2 below) needs libcanard's `canard_request`/`canard_respond` to
> accept an interface bitmap (like the multicast `tx_push` path already does) so service transfers spool only on the
> active interfaces. libcanard currently forces `CANARD_IFACE_BITMAP_ALL` on these calls with no override, so this
> cannot be fully fixed in `cy_can` alone. Coordinate an upstream libcanard change (add the bitmap parameter/variant),
> then wire `cy_can` to pass `ibm`. Until then, only the local workaround (option 1 — require
> `iface_count == CANARD_IFACE_COUNT`) is available in-tree.

## Summary
`canard_request`/`canard_respond` spool service transfers on **all** `CANARD_IFACE_COUNT` (compile-time, default 2)
interfaces with no bitmap parameter, while `v_spin` polls only the runtime `iface_count` interfaces. Frames for
phantom interfaces are never drained by a socket; they are reclaimed by libcanard's `tx_expire` at their ~1 s
deadline, so it is transient TX-queue/memory **waste** (not a permanent leak), but it recurs on every ACK, RPC
response, unicast publication, unicast gossip, and scout response whenever `iface_count < CANARD_IFACE_COUNT`.

## Location
- `cy_can/cy_can.c:721` — `canard_request(...)` (internally `tx_push(CANARD_IFACE_BITMAP_ALL, …)`), no iface bitmap.
- Contrast: multicast paths use `ibm = (1 << iface_count) - 1` correctly.
- `v_spin` drains only `ibm` interfaces; `canard_pending_ifaces` reports the phantom iface as pending.
- `CANARD_IFACE_COUNT` = 2 (`canard.h:53`); common single-iface setup: `cy_can_socketcan_new(1, …)`.

## Mechanism
Service transfers are enqueued on iface 1 (phantom) as well as iface 0 (real). Only iface 0 is polled/drained, so the
iface-1 copies sit in the queue until `tx_expire` reclaims them at deadline. On a small TX queue, the phantom copies
can occupy slots long enough to force sacrifices of real frames between expiries.

## Fix direction
Choose one:
1. In `cy_can_new`, require `iface_count == CANARD_IFACE_COUNT` (reject otherwise), making the runtime and
   compile-time interface counts agree so no phantom spooling occurs. Simplest, but forces users to compile
   `CANARD_IFACE_COUNT` to match their real interface count.
2. Preferred if libcanard supports it: pass an interface bitmap to `canard_request`/`canard_respond` (or use a
   variant) so service transfers spool only on `ibm`, matching the multicast paths. May require a libcanard change.

## Regression test (required)
- Add a CAN test with a single runtime interface on a 2-iface build that issues several unicast/service transfers
  (e.g. reliable RPC responses) and asserts no phantom-interface frames accumulate: `canard_pending_ifaces` reflects
  only the real interface after draining, and a small TX queue is not exhausted by the churn. Must fail on pre-fix
  code (phantom iface stuck pending / queue pressure), pass after.
- If option 1 is chosen, the regression test asserts `cy_can_new`/`cy_can_socketcan_new(1,…)` on a 2-iface build is
  rejected (or the constraint is otherwise enforced) so the mismatch cannot occur silently.
- Wire into `cy_can/tests` + `ctest`.

## Acceptance criteria
- [ ] Single-interface operation no longer spools undrained frames on phantom interfaces (or the mismatch is rejected).
- [ ] `canard_pending_ifaces` reports only real interfaces after draining.
- [ ] A modest TX queue is not exhausted by unicast churn under single-iface operation.
- [ ] Multicast paths and redundant (2-iface) operation unchanged; CAN suite green.

## Verification notes (adversarial cross-check)
- I will drive a burst of unicast/service transfers on a 1-iface/2-build config and inspect pending-iface state and
  TX-queue occupancy across spins.
- I will confirm the genuine redundant-interface case (iface_count == 2) still spools on both and both drain.
- If a bitmap approach is used, I will confirm scout responses and unicast gossips also route through it.
- I will confirm `tx_expire` reclamation is not the only thing preventing exhaustion (i.e. the fix actually stops the
  waste, not merely relies on the 1 s timer).
