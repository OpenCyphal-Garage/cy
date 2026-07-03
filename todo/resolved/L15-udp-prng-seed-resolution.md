# L15 — UDP PRNG seeded from `time(NULL)` (1-second resolution)

- **Severity:** 🟡 LOW (report L-15 / U-F3)
- **Confidence:** verified (code trace)
- **Subsystem:** `cy_udp_posix/cy_udp_posix.c`
- **Status:** RESOLVED

## Summary
The driver's PRNG state is seeded from `time(NULL)` (1 s resolution). With the manual constructor and a **fixed** UID,
two node starts within the same wall-clock second produce an identical transfer-ID stream; a receiver's libudpard
duplicate-history then rejects the "new" node's early transfers until the session expires (~30 s). The default
constructor uses a per-boot random EUI-64 and is unaffected.

## Location
- `cy_udp_posix/cy_udp_posix.c:842` — `self->prng_state = (uint64_t)time(NULL);`
- Consumed by `prng64` (cy_udp_posix.c:142) for the `udpard_tx` transfer-ID seed and `v_random`.

## Fix direction
Mix higher-resolution / higher-entropy sources into the seed: `clock_gettime(CLOCK_MONOTONIC)` nanoseconds,
`getpid()`, and/or a read from `/dev/urandom` (already used by `eui64.h`). Keep it dependency-light and portable
within the POSIX driver.

## Regression test (required)
- Add a test that constructs two driver instances via the manual constructor with the **same** fixed UID within the
  same second (or with `time()` seam pinned) and asserts their initial PRNG outputs / transfer-ID seeds differ. Must
  fail (identical) on pre-fix code, pass after.
- If `time()` cannot be pinned in the harness, factor the seed computation into a testable helper and assert two calls
  with the same `time` but different pid/monotonic/urandom inputs diverge.
- Wire into `cy_udp_posix/tests` + `ctest`.

## Acceptance criteria
- [ ] Two same-second, same-UID manual constructions yield distinct PRNG streams / transfer-ID seeds.
- [ ] Seeding remains portable within the POSIX driver (no new hard deps beyond what `eui64.h` already uses).
- [ ] Default (random EUI-64) construction unaffected; UDP suite green.

## Verification notes (adversarial cross-check)
- I will construct two instances back-to-back with a fixed UID and confirm divergent early transfer-IDs (and that a
  receiver would not reject the second node's transfers as duplicates).
- I will confirm the seed still varies across reboots and processes.
