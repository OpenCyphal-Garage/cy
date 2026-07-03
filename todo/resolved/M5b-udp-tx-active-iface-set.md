# M5b — libudpard TX: same compile-time-max vs runtime-active interface gap (UDP mirror of M5)

- **Severity:** 🟠 MEDIUM (derived from M5 during the 2026-07-02 design discussion; no separate review finding)
- **Confidence:** verified after confirming the libudpard TX API
- **Subsystem:** `lib/libudpard` (`udpard_tx_t`) + `cy_udp_posix/cy_udp_posix.c`
- **Status:** RESOLVED — coordinated **libudpard change**; do with/after [M5](M5-can-tx-active-iface-set.md)
- **Sibling:** [M5](M5-can-tx-active-iface-set.md) — the libcanard / `cy_can` original.

## Summary
The same class of defect as M5, on the UDP transport. libudpard's TX (`udpard_tx_t`) models redundant interfaces with
a compile-time maximum, while the runtime-active set may be smaller; "send to all" / redundant fan-out can then spool
onto phantom interfaces that no socket drains — transient TX waste, exactly as in M5. Apply the same
**instance-level active-interface set** design to `udpard_tx_t`, preserving any legitimate per-transfer publish
selection (the time-sync case) and never adding per-transfer selection where the semantics don't call for it.

## Confirmed TX model
- `udpard_tx_push()` preserves a per-transfer interface bitmap for multicast publications.
- `udpard_tx_push_unicast()` derives the candidate set from per-interface remote endpoints.
- `udpard_tx_t.iface_bitmap`, initialized by `udpard_tx_new()`, masks both paths before enqueue.
- `cy_udp_posix` owns the runtime active set as `self->iface_bitmap` based on valid local interface addresses.

## Fix design
Mirroring M5:
1. Add an **active-interface set** (bitmap) to `udpard_tx_t`, established at init (validate within the compile-time
   max; zero is accepted upstream as listen-only). Bitmap for the same reasons as M5 (non-contiguous active set for
   failover; matches any existing iface-bitmap types in udpard).
2. Redundant / unicast fan-out uses the instance active set instead of a compile-time "all."
3. **Preserve** any per-transfer publish interface selector udpard already has; interpret it as `requested & active`
   so a phantom interface is unrepresentable. **Do not add** per-transfer selection to paths that don't need it.
4. Keep the distinction between the active set (gates *enqueue*) and any per-poll / socket-writability readiness the
   driver already tracks (gates *transmit*) — do not conflate them (the M5 trap).

## Regression test
- Upstream libudpard tests verify the TX queue masking directly.
- Cy local tests keep the one-active-interface POSIX fixture and assert public-observable publish/RPC traffic produces
  no inactive-interface TX socket errors.

## Acceptance criteria
- [x] libudpard: redundant/unicast fan-out and any "all" idiom never target an interface outside the instance active
  set.
- [x] Per-transfer publish selection is preserved and masked to the active set.
- [x] Inactive interfaces are unrepresentable in the TX pipeline; no phantom queue growth.
- [x] Redundant (all-active) operation unchanged; driver readiness/socket semantics unchanged.
- [x] `cy_udp_posix` fewer-than-max runtime interfaces: no phantom fan-out; UDP suite green.
- [x] Coordinated libudpard change landed + tested upstream; submodule bumped; `cy_udp_posix` wired.

## Verification notes (adversarial cross-check)
- Upstream libudpard verifies the active-set masking directly on `udpard_tx_t`.
- Cy regression coverage uses the one-active-interface POSIX fixture and checks public-observable inactive-interface
  TX error counters; direct inactive queue inspection is not exposed by the public API.
- Per-transfer publish selection is preserved and masked, and active-set vs readiness semantics are not conflated.
- Both transports tell `cy_platform` the same story: per-transfer interface selection is a publish-only concern; a TX
  instance is configured once with its active interface set.

## Sequencing
Completed with [M5](M5-can-tx-active-iface-set.md): libudpard change landed upstream, Cy bumped the submodule,
`cy_udp_posix` passes `self->iface_bitmap` to `udpard_tx_new()`, and local regressions cover the wrapper behavior.
