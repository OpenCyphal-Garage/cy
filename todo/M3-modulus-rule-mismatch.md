# M3 — DESIGN.md's modulus-selection rule does not produce the shipped subject-ID moduli

- **Severity:** 🟠 MEDIUM (spec/interop hazard) (report M-3 / CRDT-F2)
- **Confidence:** verified (arithmetic reproduced by orchestrator)
- **Subsystem:** model/docs (`model/DESIGN.md`, `model/tlaplus/Core.tla`) vs `cy/cy_platform.h`
- **Status:** OPEN

## Summary
DESIGN.md defines the modulus as "the largest prime ≤ (max subject-ID − 8191) with modulus mod 4 = 3." That rule
yields **57331 / 8380403 / 4294959083**, but the shipped constants in `cy_platform.h` are the smaller **57203 /
8378431 / 4294954663**. A second implementation written from the spec text would compute a different subject-ID for
every non-pinned topic and be wire-incompatible (violates proof assumption A1, the common deterministic mapping).

## Location
- `model/DESIGN.md:44-46` — the stated rule (and the broadcast/shard reservation described nearby).
- `cy/cy_platform.h:20-22` — `CY_SUBJECT_ID_MODULUS_16bit/23bit/32bit` = 57203 / 8378431 / 4294954663.
- `model/tlaplus/Core.tla:33` — comment cites 8380403 (the *rule's* 23-bit value, now stale vs the shipped 8378431).

## Mechanism
The shipped constants are valid primes ≡3 (mod 4) and in range, but strictly smaller than the "largest such prime,"
apparently to reserve more gossip-shard subjects (the shipped values give 140 / 1984 / 4440 shards). That reservation
rule is not written down, so the documented derivation is not reproducible.

Verification (orchestrator):
```
rule "largest prime ≤ max-8191, ≡3 mod4":  16bit 57331 (shipped 57203, Δ128)
                                            23bit 8380403 (shipped 8378431, Δ1972)
                                            32bit 4294959083 (shipped 4294954663, Δ4420)
```

## Fix direction
This is a documentation/spec fix (the code is self-consistent). Update `model/DESIGN.md` to state the *actual* rule,
including the gossip-shard reservation that explains the smaller values (i.e. how many top subject-IDs are reserved
for the broadcast subject + shards, and that the modulus is the largest prime ≡3 mod 4 not exceeding the remaining
range). Refresh the `Core.tla:33` comment to the shipped 23-bit value. Ideally add a note that independent
implementations MUST use these exact constants (or derive via the corrected rule) or they will not interoperate.

## Regression test (required)
- Add a build-time / unit assertion test that the three shipped moduli exactly satisfy the *documented* rule as
  rewritten (prime, ≡3 mod 4, and equal to "largest prime ≤ (broadcast_base − reserved_shards)" per the corrected
  formula). This turns the doc rule into an executable invariant so future edits to either the docs or the constants
  can't silently diverge again.
- The test computes the expected modulus from the corrected rule and asserts equality with `CY_SUBJECT_ID_MODULUS_*`.
  It must fail if the docs' rule and the constants disagree.
- Wire into `ctest` (e.g. extend `test_intrusive_subject_id`).

## Acceptance criteria
- [ ] DESIGN.md's modulus rule, when applied, reproduces 57203 / 8378431 / 4294954663 exactly.
- [ ] `Core.tla` comment matches the shipped 23-bit modulus.
- [ ] An executable test encodes the corrected rule and asserts it yields the shipped constants.
- [ ] Full suite green.

## Verification notes (adversarial cross-check)
- I will re-derive all three constants from the rewritten rule and confirm exact equality (my `crdt_checks.py`
  already computes both the naive-rule and shipped values).
- I will confirm the shard-count reservation described actually yields the shipped shard counts (140/1984/4440) and
  that `broadcast_subject_id` / `gossip_shard_count` in `cy_new` are consistent with the doc.
- I will check the executable test fails if either a constant or the documented reserved-shard count is perturbed.
