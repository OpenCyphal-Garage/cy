# L14 — Empty and pin-only names must be rejected (implementation is wrong; documentation is correct)

- **Severity:** 🟡 LOW (report L-14 / N-F4)
- **Confidence:** verified (code trace + existing tests assert the wrong behaviour)
- **Subsystem:** core (`cy/cy.c`, name resolution) + tests
- **Status:** OPEN

## Maintainer decision (2026-07-02)
This finding's original framing is **reversed**: the documentation in `cy.h` is **correct** — an empty name and a
pin-only name (e.g. ``""``, `#1234`) are **invalid and must be rejected**. The current implementation is **wrong**: it
resolves them to the bare namespace when a namespace is configured. Fix the implementation to match the docs, and
update the tests that currently assert the permissive behaviour.

## Summary
`cy_name_resolve` only checks the *final resolved* name for emptiness. With a non-empty namespace, `resolve("")` and
`resolve("#1234")` (empty after stripping the pin) resolve to the namespace itself, so `cy_advertise(cy, cy_str(""))`
succeeds and publishes on a topic named after the namespace. Per `cy.h`'s documented invalid-name list this should
fail with an invalid-name result.

## Location
- `cy/cy.c:5170-5221` — `cy_name_resolve`; the emptiness check at `cy.c:5208-5210` only inspects the final resolved
  name, not the user's (pre-namespace) input.
- `cy/cy.c:5184-5186` — `name_consume_pin_suffix` strips the pin; the remaining user name can be empty and is not
  rejected before namespace/home joining.
- `cy.h:677-678` — the documented invalid rows: ``""`` "empty name is not allowed" and `#1234` "name is empty after
  the pin expression is stripped, not allowed".
- Tests currently asserting the (wrong) permissive behaviour: `tests/src/test_api_name.cpp:1038`
  (`test_name_resolve_empty_name_with_namespace`) and `:1290` (`test_name_resolve_bare_pin_with_namespace`).

## Fix direction
Reject the name **before** namespace/home resolution when the user-supplied name (after stripping any pin suffix) is
empty: return the invalid-name result (`{ .name = str_invalid, .pin = UINT16_MAX }`). This makes ``""``, `#1234`,
`#0`, and pin-only inputs invalid regardless of whether a namespace is configured — matching the cy.h table. Then
**update `test_api_name.cpp`** (the two tests above) to assert the invalid result instead of the namespace fallback,
and re-check `cy_advertise`/`cy_subscribe`/`cy_remap` callers for any that relied on the old behaviour.

## Regression test (required)
- Add/adjust name-resolution tests asserting: ``resolve("")``, `resolve("#1234")`, `resolve("#0")` → invalid
  (`name.len == SIZE_MAX`, `name.str == NULL`), **both** with and without a configured namespace; and that
  `cy_advertise(cy, cy_str(""))` / `cy_subscribe(cy, cy_str(""), …)` return NULL.
- Flip the two existing `test_api_name.cpp` tests (`..._empty_name_with_namespace`, `..._bare_pin_with_namespace`)
  from asserting the namespace fallback to asserting rejection.
- A valid non-empty name with a namespace must still resolve normally (no regression).
- Wire into `ctest`; must fail on pre-fix code (currently resolves), pass after.

## Acceptance criteria
- [ ] Empty and pin-only names are rejected as invalid regardless of namespace configuration, matching `cy.h`.
- [ ] `cy_advertise`/`cy_subscribe` with an empty name return NULL.
- [ ] The two previously-permissive `test_api_name.cpp` tests are updated to assert rejection and pass.
- [ ] Valid names (with and without namespace, with and without pin) resolve unchanged.
- [ ] Full suite green.

## Verification notes (adversarial cross-check)
- I will confirm rejection happens on the *user input* (pre-namespace), so a namespace can never rescue an empty name.
- I will test pin-only variants (`#0`, `#8191`, `#1234`) and confirm all are rejected (empty base name).
- I will confirm a legitimately namespaced non-empty name (`resolve("x")` with ns `ns1` → `ns1/x`) still works, and
  that home-expansion (`~`) and absolute (`/x`) names are unaffected.
- I will grep the test suite for any other test that assumed empty-name-resolves-to-namespace and confirm it was
  updated (no test still encodes the wrong behaviour).
