# M6 — UDP `poll()` EINTR is reported as fatal `CY_ERR_MEDIA` and aborts the event loop

- **Severity:** 🟠 MEDIUM (report M-6 / U-F2)
- **Confidence:** verified (code trace)
- **Subsystem:** `cy_udp_posix/udp_wrapper.c`, `cy_udp_posix/cy_udp_posix.c`
- **Status:** RESOLVED

## Summary
If a signal interrupts `poll()`, it returns −1/EINTR; the driver maps that to `CY_ERR_MEDIA`, which `cy_spin_until`
propagates, ending the spin loop. Any ordinary signal (SIGCHLD, SIGWINCH, a profiling timer, a debugger attach) stops
the node's traffic servicing.

## Location
- `cy_udp_posix/udp_wrapper.c:298-313` — `udp_wrapper_wait`: no EINTR retry; returns `-errno` on `poll() < 0`.
- `cy_udp_posix/cy_udp_posix.c:130-140` — `err_from_udp_wrapper` maps any errno except EINVAL/ENOMEM to `CY_ERR_MEDIA`.
- `cy_udp_posix/cy_udp_posix.c:699-722` — `v_spin` breaks its loop on error.
- `cy/cy.c:4525-4539` — `cy_spin_until` returns the error and stops.

## Mechanism
EINTR is a benign, expected `poll()` outcome, not a media failure. Treating it as fatal terminates the event loop on
any signal delivery.

## Fix direction
Retry `poll()` on EINTR in `udp_wrapper_wait` (loop while `errno == EINTR`, recomputing the remaining timeout so the
overall deadline is respected). Alternatively, map `-EINTR` to a benign "no events" result so the caller simply
re-spins. Retrying with a recomputed timeout is preferred (a busy signal source shouldn't extend the wait past the
deadline).

## Regression test (required)
- Add a test that arranges a signal to interrupt the wait (e.g. install a no-op `SIGALRM`/`SIGCHLD` handler and raise
  it during the poll, or inject EINTR via a seam) and asserts `cy_spin_until` returns `CY_OK` and continues, rather
  than `CY_ERR_MEDIA`. Must fail on pre-fix code, pass after.
- If signal injection is impractical in the harness, add a unit test around `udp_wrapper_wait` with a mockable
  `poll` seam returning EINTR once then succeeding, asserting the wrapper retries and returns success.
- Wire into `cy_udp_posix/tests` + `ctest`.

## Acceptance criteria
- [ ] An EINTR from `poll()` does not terminate the event loop; the spin continues and respects the deadline.
- [ ] A repeated EINTR storm does not extend the wait past the caller's deadline (bounded by recomputed timeout).
- [ ] Genuine `poll()` errors (e.g. EBADF) still surface as `CY_ERR_MEDIA`.
- [ ] Normal traffic servicing unaffected; UDP suite green.

## Verification notes (adversarial cross-check)
- I will confirm the retry recomputes the timeout (a tight signal loop must not spin forever or overrun the deadline).
- I will confirm a real error path (non-EINTR) still returns the mapped error.
- I will run the example smoke test with a signal source present (e.g. a child process emitting SIGCHLD) and confirm
  the node keeps running.
