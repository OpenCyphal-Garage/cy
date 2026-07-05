# H2 — Pattern subscribers never bind to topics created locally after the subscription

- **Severity:** 🔴 HIGH (report H-2; independently found by 3 reviewers)
- **Confidence:** reproduced (repro test) + code trace
- **Subsystem:** core (`cy/cy.c`, topic creation / subscriber coupling)
- **Status:** RESOLVED — `topic_ensure` now routes newly created topics through `subscribers_by_pattern` and couples
  matches (same `wkv_cb_couple_new_topic` as the gossip path), then syncs the subject reader. Unlike the gossip path,
  a coupling OOM keeps the topic (it was explicitly requested locally) and reports `ON_ASYNC_ERROR`. Accepted
  limitation (documented in the `cy_diag_vtable_t::async_error` doc): a coupling lost to OOM is not retried
  automatically; with several matching patterns a partial subset may be coupled. It self-heals only when the affected
  pattern is subscribed again (which re-runs the idempotent `wkv_match` coupling scan) or when the topic is recreated.
  Regression tests: `tests/src/test_intrusive_pattern_coupling.c` (multi-root, pinned, partial-OOM, lifecycle),
  `test_api_rx.cpp::test_api_pattern_subscriber_hears_later_local_topics`, and the strengthened
  `test_api_core_contracts.cpp::test_api_core_subscribe_then_advertise_oom_sweep`.

## Summary
Three code paths create a topic, but only the gossip-driven one (for network-learned *unknown* topics) routes the new
topic against `subscribers_by_pattern`. A topic created locally by `cy_advertise*` or a verbatim `cy_subscribe` is
never matched against existing pattern roots, so a pre-existing pattern subscription silently never receives its
messages — permanently, order-dependently.

## Location
- `cy/cy.c:1712-1749` — `topic_subscribe_if_matching` (the only site calling `wkv_route(&cy->subscribers_by_pattern, …)`),
  reachable only from `on_gossip` at cy.c:2020-2023 when `cy_topic_find_by_hash` returns NULL.
- `cy/cy.c:1531-1650` — `topic_new` (no pattern routing).
- `cy/cy.c:1652-1664` — `topic_ensure` (called by `cy_advertise_client` cy.c:2099 and verbatim subscribe cy.c:3643).
- `cy/cy.c:3680` — `subscribe()` couples a *new* subscriber to existing topics, but not vice-versa for new topics.

## Mechanism
`subscribe()` couples a newly created pattern root to already-existing topics. Gossip-created topics couple to
existing pattern roots. But a locally created topic that post-dates a pattern root is coupled by neither, and later
remote gossips for it take the known-topic branch (never `topic_subscribe_if_matching`), so the gap is permanent.

## Trigger / repro
`cy_subscribe(cy,"a/*")` then `cy_advertise(cy,"a/b")` (or verbatim `cy_subscribe(cy,"a/b")`): the pattern subscriber
gets no coupling and receives nothing on `a/b`. Advertise-only case: the topic has no reader at all, so even remote
publications never reach the pattern subscriber. Reversing the order works.
- Reference case (borrow-source, NOT built): `TODO/repro-tests-reference.c :: test_pattern_subscriber_blind_to_later_local_topics`
  (asserts couplings==1 and pattern receives 0 today; control order works).

## Scope
The dominant use case — discovering topics that *remote* nodes publish — is unaffected (those go through the gossip
path, which couples). The bug bites when this node both runs a pattern subscription and *locally* originates a
matching topic.

## Fix direction
After `topic_new` succeeds in the local-creation path (in `topic_ensure`, or centrally at the end of `topic_new`),
route the new topic name through `subscribers_by_pattern` and couple matches, mirroring `topic_subscribe_if_matching`:
`wkv_route(&cy->subscribers_by_pattern, cy_topic_name(topic), topic, wkv_cb_couple_new_topic)` followed by
`topic_sync_subject_reader(topic)`. Unlike the gossip path, an OOM here should report via `ON_ASYNC_ERROR` and leave
the topic in place (do **not** destroy a locally-requested topic on coupling OOM). Watch for double-coupling if the
routing runs for topics that were *already* coupled at subscribe time (idempotency — reuse the "coupled" scan in
`wkv_cb_couple_new_subscription`).

## Regression test (required)
- Author the regression in the canonical test file (see Fix direction), borrowing & flipping the reference case `test_pattern_subscriber_blind_to_later_local_topics` to assert the *fixed* behaviour: pattern-then-advertise
  and pattern-then-verbatim-subscribe both yield a coupling and the pattern subscriber receives the message.
- Add an advertise-only variant (pattern sub + local advertise, remote publishes) confirming the reader now exists
  and the pattern subscriber receives remote traffic.
- Add an idempotency check: creating the topic must not double-couple an already-coupled root (no duplicate delivery).
- Wire into `ctest`; must fail on pre-fix code, pass after.

## Acceptance criteria
- [ ] A locally created topic (advertise or verbatim subscribe) couples to every matching pre-existing pattern root.
- [ ] The pattern subscriber receives messages on such topics (both locally- and remotely-published).
- [ ] No double coupling / duplicate delivery when the topic was already coupled.
- [ ] Coupling OOM on a local topic reports an async error but does not destroy the topic.
- [ ] Full suite green, including pinning/pattern e2e tests.

## Verification notes (adversarial cross-check)
- I will test both orderings (pattern-first and topic-first) and both creators (advertise, verbatim subscribe).
- I will test a pattern with `*` and one with `>` against the same topic to ensure multi-root coupling.
- I will force OOM during the new coupling routine and confirm the topic survives with an async error (not destroyed,
  no leak, no dangling coupling).
- I will confirm substitutions are correctly recorded for the newly coupled pattern (so `cy_subscriber_substitutions`
  returns the right tokens), matching the gossip-path behaviour.
- Regression guard: confirm advertise-before-subscribe (the previously-working order) still works and isn't
  double-coupled by the new routing.
