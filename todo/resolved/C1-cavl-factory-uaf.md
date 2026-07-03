# C1 — AVL tree mutated inside a `cavl2_find_or_insert` factory → heap use-after-free

- **Severity:** 🛑 CRITICAL (report C-1)
- **Confidence:** reproduced under AddressSanitizer (SEGV) + code trace
- **Subsystem:** core (`cy/cy.c`, depends on `lib/cavl2.h` contract)
- **Status:** RESOLVED

## Summary
Two cavl2 factory callbacks free nodes from the very AVL tree that `cavl2_find_or_insert` is in the middle of
inserting into. `cavl2_find_or_insert` captures the parent slot pointer *before* calling the factory, then writes the
new node through that pointer and rebalances — so a factory-side removal can free the captured parent (or leave the
slot pointing at a live subtree), and the subsequent write corrupts the heap.

## Location
- `cy/cy.c:3061-3064` — `dedup_factory()` calls `dedup_drop_stale(ctx->owner, ctx->now)`.
- `cy/cy.c:3395-3398` — `reordering_cavl_factory()` calls `reordering_drop_stale(outer->subscriber, outer->now)`.
- Call sites feeding those factories: `cy/cy.c:3448` (dedup, in `on_message`), `cy/cy.c:3497` (reordering, in `on_message`).
- Contract being violated: `lib/cavl2.h:444-467` — `up` and `n = &up->lr[x]` captured at lines 452-457, written at
  line 459 (`*n = out`), then `cavl2_impl_retrace_on_growth(out)` at 464.
- `dedup_drop_stale` cy.c:3042-3052 and `reordering_drop_stale` cy.c:3373-3383 both do `cavl2_remove` + `mem_free`
  on the same tree (`owner->sub_index_dedup_by_remote_id` / `subscriber->index_reordering_by_remote_id`).

## Mechanism
`cavl2_find_or_insert` traverses to the insertion point, remembering `up` (parent) and `n` (address of the child slot
to overwrite). It then calls the factory to allocate the node. Both Cy factories run a stale-sweep that removes and
frees entries of the same tree. With a single stale node, that node *is* `up`; freeing it makes `*n = out` a write
through freed memory. With several stale nodes, rebalancing rotations move subtrees so `n` points into a relocated or
freed node. `cavl2_impl_retrace_on_growth` then walks the corrupted structure.

## Trigger / repro
A topic accumulates ≥1 per-remote dedup entry (reliable publishers) or reordering state (ordered subscribers); the
entry goes idle for > `SESSION_LIFETIME` (60 s) and has **not** yet been swept by the once-per-`poll()`-spin
round-robin GC (`poll()` at cy.c:4509/4515); then a reliable (or ordered) message from a **new** `remote_id` arrives
and its insertion fires the in-factory stale purge. No adversary, no OOM — ordinary long-running behaviour.

- Reference case (borrow-source, NOT built): `TODO/repro-tests-reference.c :: test_dedup_factory_mutates_tree_during_insert`
  (gated behind `-DCY_REVIEW_RUN_UNSAFE` because it corrupts the heap; run standalone under ASan).
- Observed: `AddressSanitizer: SEGV in cavl2_impl_rotate (lib/cavl2.h:356) ← cavl2_find_or_insert (464) ← on_message (cy.c:3448)`.

## Fix direction
Hoist the stale-sweep out of the factories to the call sites, executing it **before** `cavl2_find_or_insert` — exactly
the pattern `poll()` already uses safely (it calls `dedup_drop_stale` / `reordering_drop_stale` outside any insert).
- Move `dedup_drop_stale(topic, message.timestamp)` to `on_message` just before the dedup `cavl2_find_or_insert`
  (cy.c:3448), and delete the call from `dedup_factory`.
- Move `reordering_drop_stale(sub, message.timestamp)` to just before the reordering `cavl2_find_or_insert`
  (cy.c:3497), and delete the call from `reordering_cavl_factory`.
- (Optional, defensive) add a one-line contract note in `lib/cavl2.h` that a factory must not mutate the target tree.

Blast-radius check already done: of the eight cavl factories in cy.c, only these two mutate their own tree
(`association_`, `request_future_remote_`, `writer_`, `reader_`, `future_index`, and the trivial factory do not),
so the fix is confined to these two sites.

## Regression test (required)
- Borrow `test_dedup_factory_mutates_tree_during_insert` from `TODO/repro-tests-reference.c` into a canonical,
  build-wired intrusive test (e.g. `tests/src/test_intrusive_dedup.c`, or a new registered target). Drop the
  reference file's `CY_REVIEW_RUN_UNSAFE` gate — after the fix the case no longer corrupts the heap — and assert it
  runs cleanly (no ASan report, no crash) with the same setup (≥1 stale dedup entry present when a new remote
  inserts), and that the stale entry was reaped and the new entry created.
- Add a sibling test for the **reordering** factory (`reordering_cavl_factory`): stale reordering state present, new
  `(remote,topic)` inserts, no corruption. Add a multi-stale-node variant (≥8 entries) so tree rotation on removal is
  exercised, not just the single-node root-free case.
- Both must be registered in `tests/CMakeLists.txt` so `ctest` runs them, and be exercisable under AddressSanitizer.
- The tests must fail (SEGV/ASan) when run against the pre-fix source and pass after — verifiable by `git stash`.

## Acceptance criteria
- [ ] Neither `dedup_factory` nor `reordering_cavl_factory` calls any `cavl2_remove`/`mem_free` on the tree under
      insertion (no tree mutation inside any factory).
- [ ] Stale sweeping still happens on the reliable-message and ordered-message receive paths (not silently dropped).
- [ ] `test_dedup_factory_mutates_tree_during_insert` passes cleanly under AddressSanitizer (no SEGV, no UAF report),
      both with asserts on and `-DNDEBUG`.
- [ ] An analogous reordering-path stale-sweep-during-insert test also passes under ASan (add one if absent).
- [ ] Full suite green (96 baseline targets + the new regression target(s)); clang-tidy/cppcheck clean.

## Verification notes (adversarial cross-check)
- I will rebuild the repro standalone under `-fsanitize=address` **and** `-fsanitize=address,undefined`, both with
  and without `-DNDEBUG`, and confirm no UAF/OOB.
- I will construct a *multi-stale-node* case (≥8 stale entries so the tree rotates on removal, not just a root free)
  to ensure the fix isn't merely masking the single-node case.
- I will confirm the moved sweep uses the **message timestamp** (not a stale `now`) so entries expire correctly, and
  that a genuinely-new remote still gets an entry created after the sweep (no accidental drop of the incoming message).
- I will verify `poll()`'s existing sweep calls are unchanged and not doubled.
- Heap-accounting check: `guarded_heap` fragment/byte counts return to zero on teardown in the reordering variant.
