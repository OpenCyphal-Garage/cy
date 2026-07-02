# M5b — libudpard TX: same compile-time-max vs runtime-active interface gap (UDP mirror of M5)

- **Severity:** 🟠 MEDIUM (derived from M5 during the 2026-07-02 design discussion; no separate review finding)
- **Confidence:** by analogy to M5 (verified) — **the libudpard TX API must be confirmed first (see below)**
- **Subsystem:** `lib/libudpard` (`udpard_tx_t`) + `cy_udp_posix/cy_udp_posix.c`
- **Status:** OPEN — coordinated **libudpard change**; do with/after [M5](M5-can-tx-active-iface-set.md)
- **Sibling:** [M5](M5-can-tx-active-iface-set.md) — the libcanard / `cy_can` original.

## Summary
The same class of defect as M5, on the UDP transport. libudpard's TX (`udpard_tx_t`) models redundant interfaces with
a compile-time maximum, while the runtime-active set may be smaller; "send to all" / redundant fan-out can then spool
onto phantom interfaces that no socket drains — transient TX waste, exactly as in M5. Apply the same
**instance-level active-interface set** design to `udpard_tx_t`, preserving any legitimate per-transfer publish
selection (the time-sync case) and never adding per-transfer selection where the semantics don't call for it.

## FIRST STEP — blocking (confirm the udpard TX model before designing)
Read `lib/libudpard/libudpard/udpard.h` (TX side) and `cy_udp_posix/cy_udp_posix.c`, and confirm:
- How `udpard_tx` fans a transfer out to redundant interfaces: a per-transfer redundant-interface argument? a
  compile-time max analogous to `CANARD_IFACE_COUNT`? an "all interfaces" idiom analogous to `CANARD_IFACE_BITMAP_ALL`?
- Whether udpard's TX distinguishes publish from request/response-equivalent (unicast) paths, and how each chooses
  interfaces — i.e. whether the publish-only per-transfer-selection asymmetry from M5 exists here too.
- Whether udpard publish carries a per-transfer interface selector that must be **preserved** (the time-sync-style
  need), or whether UDP has no such requirement.
- How `cy_udp_posix` currently tells udpard its interface count and how it builds per-interface TX (it maintains
  per-iface sockets; `cy_udp_posix` review noted VLAs sized by iface/reader count).

Only once the above is confirmed, finalize the fix shape. If udpard's TX model differs materially from canard's, adapt
the design rather than force the canard shape onto it.

## Expected fix design (confirm against udpard before coding)
Mirroring M5:
1. Add an **active-interface set** (bitmap) to `udpard_tx_t`, established at init (validate non-empty, within the
   compile-time max). Bitmap for the same reasons as M5 (non-contiguous active set for failover; matches any existing
   iface-bitmap types in udpard).
2. Redundant / unicast fan-out uses the instance active set instead of a compile-time "all."
3. **Preserve** any per-transfer publish interface selector udpard already has; interpret it as `requested & active`
   so a phantom interface is unrepresentable. **Do not add** per-transfer selection to paths that don't need it.
4. Keep the distinction between the active set (gates *enqueue*) and any per-poll / socket-writability readiness the
   driver already tracks (gates *transmit*) — do not conflate them (the M5 trap).

## Regression test (required)
- `cy_udp_posix` with fewer runtime interfaces than the udpard compile-time max: issue unicast/redundant transfers and
  assert no phantom-interface fan-out and no undrained TX-queue growth attributable to inactive interfaces. Must fail
  pre-change, pass after. Wire into `cy_udp_posix/tests` + `ctest`.
- Mirror libudpard's own upstream adversarial tests for the TX active-set masking (per libudpard's testing rules):
  a single-active-of-N-compile-time config enqueues only on the active interface(s); per-transfer publish selection
  (if udpard has it) still lands on exactly the requested active interface; the empty-intersection case behaves per
  the decision taken for M5.

## Acceptance criteria
- [ ] libudpard: redundant/unicast fan-out and any "all" idiom never target an interface outside the instance active set.
- [ ] Per-transfer publish selection (if present in udpard) is preserved and masked to the active set.
- [ ] Inactive interfaces are unrepresentable in the TX pipeline; no phantom queue growth.
- [ ] Redundant (all-active) operation unchanged; driver readiness/socket semantics unchanged.
- [ ] `cy_udp_posix` fewer-than-max runtime interfaces: no phantom fan-out; UDP suite green.
- [ ] Coordinated libudpard change landed + tested upstream; submodule bumped; `cy_udp_posix` wired.

## Verification notes (adversarial cross-check)
- I will confirm the udpard TX model matches (or where it diverges, that the adapted design is justified) before
  accepting the fix — this file's design is provisional until the FIRST STEP is done.
- I will drive a fewer-than-max active config and confirm no frames are enqueued for inactive interfaces and no
  undrained growth; I will confirm the fix stops the waste rather than relying on any expiry timer.
- I will confirm per-transfer publish selection (if any) is preserved and masked, and that active-set vs readiness are
  not conflated.
- I will confirm both platforms end up telling `cy_platform` the same story: per-transfer interface selection is a
  publish-only concern; a TX instance is configured once with its active interface set.

## Sequencing
Do in coordination with [M5](M5-can-tx-active-iface-set.md) so the CAN and UDP transports stay symmetric. Confirm the
udpard TX API (FIRST STEP) → land + test the libudpard change upstream → bump the submodule → wire `cy_udp_posix` and
add the regression.
