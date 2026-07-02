# M5 — libcanard "send to all" targets all *compile-time* interfaces, not the runtime-active set (TX waste)

- **Severity:** 🟠 MEDIUM → low-medium (report M-5 / CAN-F3)
- **Confidence:** verified (code trace); triage corrected "leak" → transient waste
- **Subsystem:** `lib/libcanard` (`canard_t` TX) + `cy_can/cy_can.c`
- **Status:** OPEN — coordinated **libcanard API change** (design agreed with maintainer 2026-07-02)
- **Sibling:** [M5b](M5b-udp-tx-active-iface-set.md) — the libudpard / `cy_udp_posix` mirror.

## Summary
`canard_request`/`canard_respond` (and the v0 variants) enqueue on `CANARD_IFACE_BITMAP_ALL`, i.e.
`(1U << CANARD_IFACE_COUNT) - 1U` — **all compile-time** interfaces. When the runtime-active interface set is a
strict subset (e.g. a single-interface node on a 2-interface build), frames are spooled onto phantom interfaces that
no socket drains; they linger until libcanard's `tx_expire` reclaims them at their ~1 s deadline. Transient
TX-queue/memory **waste** (not a permanent leak), recurring on every ACK, RPC response, unicast gossip, and scout
response. The same superset hazard exists on the **publish** path whenever a caller reaches for `_ALL`.

## Root cause (agreed design analysis)
The active interface set is **node-level** state, but libcanard only knows the compile-time maximum
(`CANARD_IFACE_COUNT`, which sizes `canard_t.tx.pending[]`). `CANARD_IFACE_BITMAP_ALL` therefore means "all
compile-time interfaces," a potential *superset* of what the application actually uses. `cy_can` already holds the
true runtime count (`iface_count`) and threads `(1<<iface_count)-1` into every **publish** call — but
`canard_request`/`canard_respond` take no bitmap, so they cannot be told, and hardcode `_ALL`. That un-tellable path
is M5.

**Key semantic constraint (do not violate):** per-transfer interface selection is a legitimate **publish-only**
feature — e.g. time-synchronization beacons pinned to a specific bus. Requests/responses never need it: redundancy
sends them on *every* active path, so there is no legitimate per-transfer variation to express. This is exactly why
only publish carries a mask and request/respond do not. **The fix must preserve that asymmetry.**

## Location
- `lib/libcanard/libcanard/canard.h:58` — `CANARD_IFACE_BITMAP_ALL = (1U << CANARD_IFACE_COUNT) - 1U`.
- `canard.h:462-480` — `canard_request`/`canard_respond` ("Enqueue ... on all ifaces", **no** bitmap param); v0
  counterparts at `canard.h:584-606`.
- `canard.h:445-460` — `canard_publish_16b`/`_13b` (these **do** take a per-transfer `iface_bitmap` — keep it).
- `canard.h:325` — `canard_t.tx.pending[CANARD_IFACE_COUNT]`.
- `canard.h:408` — `canard_poll(self, tx_ready_iface_bitmap)` — the readiness bitmap (a *different* concept, see below).
- `cy_can/cy_can.c:721` — `canard_request(...)` (cannot constrain to the active set today).
- `cy_can/cy_can.c:38, 851, 840` — `cy_can` stores/validates `iface_count` (`iface_count <= CANARD_IFACE_COUNT`).
- `cy_can/cy_can.c:473, 758, 1025` — publish/poll compute `ibm = (1<<iface_count)-1` (the identical constant per node).

## Fix design (agreed)
Adopt an **instance-level active-interface set** in libcanard and interpret all TX against it. **Do NOT** add a bitmap
to request/respond (that path has no legitimate per-transfer selection — adding one re-creates the "thread node-state
through a per-call param" pattern that caused M5). **Do NOT** remove the publish mask (it is needed for per-interface
publish such as time sync).

### libcanard changes
1. Add an active-interface **bitmap** to `canard_t` — a `uint_least8_t`, established at `canard_new` (validate
   `active != 0` and `active <= CANARD_IFACE_BITMAP_ALL`). **Bitmap, not a count**: same cost, matches the types
   already in the API (`canard_poll`'s `tx_ready_iface_bitmap` and `canard_pending_ifaces`' return), inits trivially
   from a count (`(1<<n)-1`), and can represent a **non-contiguous** active set (e.g. iface 0 down, iface 1 up) for
   failover without renumbering slots. (Optional future: a runtime setter to update it for failover — out of scope
   here; note it and leave the pending-queue drain/expire semantics of a deactivated interface for a follow-up.)
2. `canard_request`/`canard_respond` (and v0 variants) enqueue on the instance **active set** instead of
   `CANARD_IFACE_BITMAP_ALL`.
3. Publish keeps its per-transfer `iface_bitmap`, but the **effective** set becomes `requested & active`. A phantom
   interface thereby becomes **unrepresentable**. `CANARD_IFACE_BITMAP_ALL` survives, redefined semantically to
   "all *active*": a publish passing it is masked to the active set.
4. **Empty-intersection case — OPEN QUESTION for maintainer:** if `requested & active == 0`, propose treating it as an
   invalid argument / nothing enqueued (bump a suitable `err` counter). Confirm the desired behavior before coding.

**Do NOT conflate the active set with `canard_poll`'s `tx_ready_iface_bitmap`.** The active set gates which
interfaces a transfer is *enqueued* for; the poll readiness bitmap gates which *enqueued* frames are handed to `tx()`
this instant (writable mailboxes). Poll's parameter is unchanged and remains per-poll dynamic. Mask publish against
the **active set**, never against the readiness bitmap.

### cy_can changes (after the submodule bump)
- Pass the active set to `canard_new` (`cy_can` already has `iface_count`; init `active = (1<<iface_count)-1`).
- Publish sites may pass `CANARD_IFACE_BITMAP_ALL` (now = active) instead of recomputing `ibm`; the request path needs
  nothing further. `canard_poll` still receives the driver's genuine readiness bitmap (unchanged).
- Note: `cy_can` itself always publishes to the full active set, so the publish-masking is transparent for `cy_can`;
  the per-transfer mask matters only for other library users (the time-sync case), which is why it stays in the API.

## Regression test (required)
**libcanard (upstream, adversarial — per libcanard's own testing rules):**
- 2-interface build with active set `{0}` only: issue several service transfers (request + response) and assert **no**
  frame is ever enqueued on `pending[1]`, `canard_pending_ifaces` reports only iface 0, `tx.queue_size` reflects only
  real frames, and a small `tx_queue_capacity` is not exhausted / does not force `tx_sacrifice` across the churn. Must
  fail pre-change (phantom `pending[1]`), pass after.
- Publish masking: active `{0}`, publish requesting `_ALL` → only iface 0; publish requesting `{1}` (disjoint) → the
  empty-intersection behavior decided above. Active `{0,1}`, publish requesting `{0}` → only iface 0 (time-sync case
  preserved).
- Redundant case unchanged: active `{0,1}`, request/response and `_ALL` publish enqueue on both.

**cy_can:**
- Single runtime interface on a 2-interface build issuing reliable RPC responses: `canard_pending_ifaces` reflects
  only the real interface after draining; a modest TX queue survives the churn. Must fail pre-change, pass after.
- Wire into `cy_can/tests` + `ctest`.

## Acceptance criteria
- [ ] libcanard: request/respond and `_ALL` publish never enqueue on an interface outside the instance active set.
- [ ] Per-transfer publish selection still works for a specific active interface (time-sync case preserved).
- [ ] Empty-intersection publish behaves per the agreed decision (documented).
- [ ] `canard_pending_ifaces` cannot report an interface outside the active set.
- [ ] Redundant (all-active) operation unchanged; `canard_poll` readiness semantics unchanged.
- [ ] `cy_can` single-iface-on-2-build: no phantom pending; TX queue not exhausted by unicast churn; CAN suite green.
- [ ] Coordinated libcanard change landed + tested upstream; submodule bumped; `cy_can` simplified.

## Verification notes (adversarial cross-check)
- I will drive a single-active-of-two-compile-time config and inspect `pending[]`, `queue_size`, `pending_ifaces`, and
  `tx_sacrifice`/`tx_expiration` counters across spins — the fix must *stop* the waste, not merely rely on `tx_expire`.
- I will confirm the publish mask is ANDed with the active set (phantom unrepresentable) and that a genuine
  per-interface publish (subset of active) still lands on exactly that interface.
- I will confirm request/respond gained **no** per-transfer bitmap (asymmetry preserved) and that `_ALL` now means
  "all active."
- I will confirm the active set and the poll readiness bitmap are not conflated (enqueue per active set, transmit per
  readiness).
- I will confirm the redundant 2-interface path still enqueues on both and both drain.

## Sequencing
1. libcanard: implement + adversarial tests; land upstream (an API change — `canard_new` gains the active-set arg and
   request/respond behavior changes; version-bump accordingly).
2. Bump the libcanard submodule in `cy`.
3. `cy_can`: wire the active set at construction, simplify publish, add the `cy_can` regression.
4. Mirror on the UDP side — see **[M5b](M5b-udp-tx-active-iface-set.md)**.
