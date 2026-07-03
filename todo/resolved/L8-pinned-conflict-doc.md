# L8 — DESIGN.md overclaims pinned-topic conflict arbitration (documentation fix; implementation is fine)

- **Severity:** 🟡 LOW (documentation only) (report L-8 / CRDT-F3)
- **Confidence:** verified (code trace; behaviour is intentional)
- **Subsystem:** docs (`model/DESIGN.md`) — **no code change**
- **Status:** RESOLVED

## Maintainer note
The **implementation is correct/intentional**; this is a **documentation fix**. Do not change code.

## Summary
Pinned topics are deliberately excluded from the subject-ID collision index, so two *different* topics pinned to the
same subject-ID are never collision-arbitrated — they coexist and are demultiplexed by the per-message topic hash
(v1.0-style subject sharing, as the code comments and README describe). But `DESIGN.md` claims "an older pinned topic
may displace a newer conflicting pin," which is not implemented and contradicts the intended design.

## Location
- `cy/cy.c:126-130`, `cy/cy.c:1423-1428` ("No collision detection is needed"), `cy/cy.c:1337-1343`
  (`topic_find_by_subject_id` excludes pinned) — the intentional exclusion.
- `model/DESIGN.md:202-206` — the incorrect claim about pinned displacement.
- Note: same-hash *divergence* between a pinned and unpinned replica of one topic **is** handled correctly (not part
  of this fix).

## Fix direction
Update `model/DESIGN.md:202-206` to state the actual behaviour: conflicting *distinct* pinned topics on the same
subject-ID **coexist** (shared subject, per-message hash demultiplexing), and pinned topics are not
collision-arbitrated against each other or against auto-allocated topics (their subject-ID ranges are disjoint). Keep
the accurate description of same-hash divergence handling.

## Regression test (required)
- Behavioural lock: add/confirm an e2e test that two distinct topics pinned to the same subject-ID coexist and each
  receives only its own traffic (per-hash demux), documenting the intended design so a future "fix" can't silently
  change it. (This is the executable counterpart to the doc correction.) Wire into `ctest` if not already covered by
  the pinning cohabitation tests.
- Since the change is doc-only, the "fails before / passes after" criterion applies to the doc assertion: the doc must
  now match the tested behaviour.

## Acceptance criteria
- [ ] `DESIGN.md` no longer claims pinned-vs-pinned displacement; it describes coexistence + hash demux.
- [ ] An e2e test locks in the coexistence behaviour (two distinct pins on one subject, correct per-hash delivery).
- [ ] No code change to the pinned-topic path.
- [ ] Full suite green.

## Verification notes (adversarial cross-check)
- I will confirm the doc now matches `cy.c` exactly and that same-hash divergence handling is still described.
- I will run the pinning cohabitation e2e and confirm two distinct pins on one subject deliver only their own traffic.
