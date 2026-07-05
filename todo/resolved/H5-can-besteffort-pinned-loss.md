# H5 — Best-effort publish on a custom-named pinned topic is silently dropped (CAN)

- **Severity:** 🔴 HIGH (report H-5 / CAN-F1)
- **Confidence:** reproduced by the CAN agent (control vs affected topic)
- **Subsystem:** `cy_can/cy_can.c`
- **Status:** RESOLVED

## Resolution
Chose option 1 with automatic detection (no new API, no user config). `v_subject_writer_send` now takes the
headerless v1.0 13-bit plane for a pinned best-effort publish **only** when the message's topic hash (header
byte offset 8) equals `rapidhash(decimal(sid))` — i.e. the `N#N` compat idiom. This is exactly the condition
the receiver's fabricated phony header (`build_phony_header`) matches, so when the 13-bit plane is used the
message is delivered rather than silently dropped; every other name (e.g. `foo/bar#611`) falls through to the
16-bit plane with the real header and is delivered. The TX detector (`topic_is_compat_named`) and the RX
fabricator share one `compat_topic_hash()` helper so they cannot drift. Regression tests (both fail pre-fix,
pass after): `test_api_can_pubsub_pinned_best_effort_custom_name_uses_v11_plane` (custom-named delivery on the
16-bit plane) and `test_api_can_pubsub_multitenant_pinned_best_effort_delivers_and_filters` (`foo#1234` +
`bar#1234` on one shared subject-ID, each delivered and hash-filtered). README "Compatibility with Cyphal/CAN
v1.0" documents the `N#N`-selects-13-bit-plane behaviour.

## Summary
For a pinned subject (`sid ≤ 8191`) published best-effort, the CAN driver strips Cy's header and sends on the
headerless Cyphal/CAN v1.0 13-bit plane. The receiver fabricates a header hash from the decimal subject-ID string, so
only topics literally named `"<sid>"` match. Any other name — including the README's documented `foo/bar#1234` and
the multi-tenant `foo#1234`/`bar#1234` — hash-misses and the message is dropped. `cy_publish` still returns `CY_OK`.

## Location
- `cy_can/cy_can.c:476-497` — `v_subject_writer_send`: `use_13b = pinned && best_effort`; if/else, no 16-bit fallback.
- `cy_can/cy_can.c:524-532` — `build_phony_header`: `hash = rapidhash(decimal(subject_id))`.
- Receiver mismatch surfaces at `cy/cy.c:4799` (`cy_topic_find_by_hash` returns NULL → not delivered).

## Mechanism
Best-effort + pinned takes the bare 13-bit v1.0 path (headerless). The receiver can't recover the topic name, so it
manufactures `hash = rapidhash("611")` for subject 611. A topic named `foo/bar#611` has hash `rapidhash("foo/bar")`,
which never equals `rapidhash("611")`, so `cy_topic_find_by_hash` misses. Reliable publications on the *same* pinned
topic use the 16-bit plane with the real header and work — which masks the loss and makes it look intermittent.

## Trigger / repro
Two v1.1 nodes on `foo/bar#611`, default `cy_publish` (best-effort). Agent repro: control `610#610` delivers;
`foo/bar#611` best-effort is lost; `cy_publish_reliable` on the same topic delivers.

## Fix direction
Options (choose per project intent — confirm with maintainer, but the review recommends the first):
1. Use the **16-bit plane with the real header** for pinned v1.1 best-effort traffic, and gate the headerless 13-bit
   v1.0-compat path behind an explicit opt-in (so v1.0 interop is a deliberate choice, not the default that silently
   drops custom-named pinned topics).
2. If the 13-bit path must remain the default for pinned best-effort, enforce/document that pinned topics used on CAN
   must be named `N#N` (the decimal-SID form), and reject or warn on other names at advertise time so the loss is not
   silent.

## Regression test (required)
- Add a two-node (or loopback) CAN test: advertise + subscribe a **custom-named** pinned topic (e.g. `foo/bar#611`),
  `cy_publish` best-effort, assert the subscriber receives it. Also keep an `N#N`-named control. Must fail (no
  delivery) on pre-fix code, pass after.
- If option 2 is chosen instead, the regression test asserts that a custom-named pinned advertise is rejected/flagged
  rather than silently dropping — the test must still distinguish fixed from unfixed behaviour.
- Wire into `cy_can/tests` + `ctest`.

## Acceptance criteria
- [ ] A best-effort publish on a custom-named pinned topic is either delivered to a matching subscriber, or fails
      loudly at publish/advertise time — never silently dropped while returning `CY_OK`.
- [ ] `N#N`-named pinned topics still interoperate with Cyphal/CAN v1.0 as before (no regression to v1.0 compat).
- [ ] Reliable pinned publish still works; multi-tenant pinned (`foo#1234`+`bar#1234`) behaves per design.
- [ ] CAN suite green.

## Verification notes (adversarial cross-check)
- I will test the exact README examples (`foo/bar#1234`, and `foo#1234`+`bar#1234` sharing a subject) best-effort and
  confirm delivery/filtering matches the documentation.
- I will confirm v1.0 interop (`1234#1234`) is preserved if option 1 gates the 13-bit path — a v0/v1.0 peer must
  still exchange with an `N#N` topic.
- I will check the reliable path is unchanged and that gossip/discovery for pinned topics still works.
- I will confirm `cy_publish` no longer returns `CY_OK` for a message that is structurally undeliverable (if option 2).
