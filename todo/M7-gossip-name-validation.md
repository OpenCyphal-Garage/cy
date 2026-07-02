# M7 — Gossiped topic names are not charset/normalization-validated before creating & re-gossiping implicit topics

- **Severity:** 🟠 MEDIUM (hygiene/interop) (report M-7 / N-F3, L-F9)
- **Confidence:** verified (code trace); ASan-clean (no memory unsafety)
- **Subsystem:** core (`cy/cy.c`, gossip receive / implicit topic creation)
- **Status:** OPEN

## Summary
A received gossip name is accepted on length (≤200) and `rapidhash(name) == hash` only. A malfunctioning or malicious
remote can gossip names containing spaces, control bytes, wildcard tokens, pin-like suffixes, or non-normalized
separators; if one matches a local pattern, an implicit topic with that raw name is created, indexed, and re-gossiped
once — violating the wire contract "the name is normalized" on the enforcement side.

## Location
- `cy/cy.c:4940-4959` — gossip parse (only length checked).
- `cy/cy.c:1712-1749` — `topic_subscribe_if_matching` (only non-empty + `rapidhash(name) == hash` checked).

## Mechanism
No charset/normalization filter on inbound gossip names. wkv handles arbitrary bytes safely and the hash check
prevents forging a name for a *given* hash, so there is no memory-safety impact — but a non-normalized/illegal name
can be created locally and propagated, which is an interoperability/hygiene defect the design's fault-robustness goal
calls for closing.

## Fix direction
Reject inbound gossip names that are not already valid normalized names before creating an implicit topic — e.g. in
`topic_subscribe_if_matching` (or the gossip parse), require `name_normalized_len(name) == name.len` (this single
check rejects illegal characters and non-normalized forms). Optionally also reject names containing substitution
tokens (`*`/`>`) since a concrete topic name must not contain them.

## Regression test (required)
- Add a test that feeds gossips with (a) a control byte / space, (b) a non-normalized name (`a//b`, leading/trailing
  `/`), and (c) a name containing `*`/`>`, each crafted with a matching `rapidhash`, against a node with a matching
  pattern subscription; assert no implicit topic is created for the invalid names (and a valid normalized name still
  is). Must fail on pre-fix code (topic created), pass after.
- Wire into `ctest` (extend `test_intrusive_gossip` or an API-level gossip test).

## Acceptance criteria
- [ ] Inbound gossip names failing `name_normalized_len(name) == name.len` are rejected (no topic created, no re-gossip).
- [ ] Names containing substitution tokens are rejected as concrete topic names.
- [ ] Valid normalized gossip names still create implicit topics and couple to patterns as before.
- [ ] Full suite, incl. gossip tests, green.

## Verification notes (adversarial cross-check)
- I will craft gossips with matching hashes for illegal/non-normalized/tokenized names and confirm rejection at the
  acceptance boundary (not just later).
- I will confirm a legitimate normalized name still round-trips (create → couple → deliver → re-gossip).
- I will confirm the check is applied on all inbound scopes that can create topics (broadcast + unicast gossip).
- I will confirm the hash check remains (rejection is *in addition to*, not instead of, the anti-forgery guard).
