# L16 — Vestigial TTL / gossip-forwarding commentary (comment cleanup)

- **Severity:** 🟡 LOW (maintainability) (report L-16 / CRDT-F13)
- **Confidence:** verified (code trace)
- **Subsystem:** core (`cy/cy.c`) + `model/DESIGN.md` — comments/docs only
- **Status:** OPEN

## Summary
Comments reason about gossip TTL resets and multi-hop forwarding, but the wire format has **no** TTL field (the
relevant header bytes are `void24`) and there is **no** forwarding code. The stale commentary misleads maintainers
verifying the implementation against the model.

## Location
- `cy/cy.c:2026-2037` — comments discussing TTL resets / forwarding that don't exist.
- `model/DESIGN.md:222` — "gossip message with zero TTL" phrasing.
- (Cross-check the header definitions in `cy.c`/DESIGN.md confirm the field is reserved `void`, not a TTL.)

## Fix direction
Remove or correct the vestigial TTL/forwarding comments in `cy.c:2026-2037` to describe what the code actually does
(urgent vs periodic vs suppressed gossip; no forwarding, no TTL). Align the `DESIGN.md:222` wording (a scout response
is an ordinary gossip; drop the "zero TTL" phrasing or explain that the field is reserved and unused). No behavioural
change.

## Regression test (required)
- Comment/doc-only change: no runtime test. The required check is a **documentation-consistency assertion** — confirm
  (by grep in review + a note in the commit) that no remaining comment references a TTL/forwarding mechanism that the
  wire format and code lack, and that the reserved header field is described as `void`/reserved. (No `ctest` entry is
  meaningful here; verification is by inspection.)

## Acceptance criteria
- [ ] No comment in `cy.c` claims a TTL field or gossip forwarding that does not exist.
- [ ] `DESIGN.md:222` wording matches the actual (no-TTL, no-forwarding) design.
- [ ] No behavioural/code change; full suite still green.

## Verification notes (adversarial cross-check)
- I will grep `cy.c` and `DESIGN.md` for "TTL"/"forward"/"hop" and confirm remaining mentions are accurate (e.g. the
  analytical model in `model/gossip_propagation.ipynb` may legitimately discuss TTL for epidemic models — that's fine;
  the *protocol* comments must not imply an implemented TTL).
