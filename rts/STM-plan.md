# STM fix checklist

This file tracks open work items for the `stm-improvements` branch. The design
rationale behind each item lives in `rts/STM-free-applicative.md`; the full
findings with line-number evidence are in `FINDINGS.md`.

Items marked `[x]` are done; `[ ]` remain open.

## Critical bugs (must fix before merge)

- [ ] **C-1 / M-2: Watch-queue GC crash.** Replace the `NULL` terminator on the
  per-thread `StgTVarWatchQueue` list with `stg_END_STM_WATCH_QUEUE_closure`.
  Change all `q != NULL` guards (`register_wait`, `validate_and_lock_registered`,
  `unlock_registered_prefix`, `remove_wait_queue_entries_from_list`,
  `trec_wait_list`) to compare against `END`. Add an explicit `checkClosure` case
  for the watch queue to the sanity checker.

- [ ] **C-2: No incremental validation (zombie transactions).** `validate#` is
  wired as a primop and called in `evalSTM` before `SBind` continuations and in
  `runAtomically` before blocking. Verify the RTS implementation of `validate#`
  is complete and sound (lock-free pointer-equality check, returns 0/1).

- [ ] **C-3: `orElse`/`catchSTM` wait-set clobbering.** Confirmed absent in the
  shipped two-list model: the monotone `txWait` accumulates across `orElse`
  branches without mid-flight `clearRegistrations#`, and `runAtomically` registers
  exactly once. Verify with the wait-union test (H-8) that no path reinstates the
  mid-flight-registration pattern.

- [ ] **C-4: `registerLogRange#` missing from JS `genPrim`.** Add a
  `RegisterLogRangeOp` case calling `h$registerLogRange` (+ `hdRegisterLogRangeStr`).

- [ ] **C-5: `stmCommitLog#` JS handler binds 5 args; correct arity is 4.** Change
  the destructure from `[tvars, expected, newvals, flags, len]` to
  `[tvars, expected, newvals, len]`.

## High

- [ ] **H-1: `free_stg_tvar_watch_queue` zeroes traced pointer fields without
  nonmoving barriers.** Preferred fix: stop zeroing on free — `stmPreGCHook`
  drops the freelist wholesale, so zeroing buys no GC-safety. Alternative: push
  old values under `IF_NONMOVING_WRITE_BARRIER_ENABLED`.

- [ ] **H-2: `register_wait` overwrites `q->expected` in place with no write
  barrier.** Add `IF_NONMOVING_WRITE_BARRIER_ENABLED { updateRemembSetPushClosure
  (cap, q->expected); }` before the store.

- [ ] **H-7: `interface-stability` baselines stale.** Freeze the primop set, then
  regenerate `ghc-prim-exports.stdout` and the `-mingw32` variant.

- [ ] **H-8: `stm_orElse_wait_union` does not test the wait-set union.** Add cases
  that wake when only the *left-branch* TVar is written and when only a TVar read
  *before* the `orElse` is written. Both must wake under a timeout.

## Medium

- [ ] **M-1: `sort_log_arrays` permutes pointer slots in-place without nonmoving
  barriers.** Push old slots under `IF_NONMOVING` before permutation, or sort in
  the Haskell layer (pre-marshalling) to avoid mutating already-traced arrays.

- [ ] **M-3: Single `writeTVar` fast path.** Done: `atomically`'s `fastPath`
  handles `SPrim (PWrite tv val)` via `commitSingleWrite`, which loops on conflict
  with no fragment analysis.  Mark complete if `commitSingleWrite` is verified.
  - [x] `PWrite` fast path in `fastPrim`.

- [ ] **M-4: `TArray.newArray` uses `unsafeIOToSTM`, breaking the applicative
  fragment.** Reintroduce an in-fragment allocation node or replace the
  `unsafeIOToSTM` with `traverse (const (newTVar e))`.

- [ ] **M-5: `base-exports` baseline describes the old `STM` newtype.** Regenerate
  after confirming the `STM` constructor no longer leaks (`stmPlan` must remain
  internal).

- [ ] **M-7: `registerWait#` primop + JS `h$stmWait`/`h$stmResumeRetry_e` are
  dead.** Remove the `registerWait#` primop surface and the dead JS closures.

- [ ] **M-8: `UnliftedTVar1/2` `.stdout` orphans.** Delete orphaned `.stdout`
  files; add minimal unlifted-content coverage through the current surface.

- [ ] **M-9: `stm_orElse_rollback` too weak.** Add: read-after `atomically` to
  confirm discarded writes don't leak; a deterministic exactly-once conflict test;
  `throwTo`-mid-transaction coverage.

- [ ] **M-10: No targeted tests for `mfix`/`SFix` or nested-orElse.** Add a
  recursive `mfixSTM`, a retrying/throwing `mfixSTM`, and a 2+-deep nested
  `orElse` that asserts a wake on *any* branch's read set.

## Low

- [ ] **L-1: `config_use_read_phase` invariant undocumented.** Add assertion/comment
  at `commit_log_entries` documenting that every committer that changes
  `current_value` must bump `num_updates`.

- [ ] **L-2: Per-attempt O(n²) insertion sort in commit hot path.** Switch to O(n
  log n) (sort an index permutation) for larger log sizes; insertion sort is fine
  for tiny logs.

- [ ] **L-4: `logLookup`/`writeTVarTx` coercion sites.** Document the
  per-transaction fixed-type invariant; the single coercion site is already
  confined to `coerceVal` in `logLookup`.

- [ ] **L-5: Dead JS helpers.** Delete `h$stmWait`, `h$stmResumeRetry_e`,
  `hdReadTVar`/`hdWriteTVar` from `rts/js/stm.js` and the corresponding exports
  in `StgToJS/Rts/Rts.hs` and `StgToJS/Symbols.hs`.

- [ ] **L-6: `emptyAny` and `STMResult`.** `emptyAny` is now a genuine fault
  (`raise#` rather than a dummy value) — verify. `STMResult` (if it still exists)
  should be replaced with the standard `(STMOutcome a, TxLog)` shape.

- [ ] **L-7: `trec->plan` field name.** Rename to `wait_queue` or `registrations`
  everywhere in `rts/STM.c` and `rts/STM.h`.

- [ ] **L-8: `mfix`/`SFix` divergence semantics.** Decided: `evalFix` uses explicit
  black-holing (MVar + `unsafeDupableInterleaveIO`), matching the `fixIO`/`fixST`
  shape, rather than a lazy `State#` knot. A non-`Ok` body leaves the MVar empty;
  forcing `ans` raises `FixIOException` via `BlockedIndefinitelyOnMVar`. This is a
  catchable exception, not a true GHC black hole — document the deviation.

## Done

- [x] Remove the stale `stmValidateNestOfTransactions` note; validation lives in
  `stmCommitLog#` and `validate#`.
- [x] `tryPeekTQueue`/`tryPeekTBQueue`/`tryPeekTChan` rewritten to avoid the
  `tryRead`/`unGet` round-trip.
- [x] `cond_lock_tvar` remembered-set fix: gate `updateRemembSetPushClosure` on
  `result == expected`.
- [x] `PWrite` fast path in `atomically`'s `fastPrim` (`commitSingleWrite`).
- [x] `funArgTy` compiler panic resolved by the thin-wrapper `STM` design.
- [x] `MonadFix STM` relocated from the `stm` submodule into `ghc-internal`
  (CPP-gated for `base >= 4.22`).

## Design decisions recorded here (do not re-open without evidence)

**Immutable `[TxEntry]` log — not mutable SoA arrays.** The mutable
structure-of-arrays design (earlier drafts: `pushScope`/`rollbackScope`/shadow
entries/`cap`/`len`/`findIndex`) was rejected. It is fragile (all the GC criticals
in FINDINGS trace to it), complex (rollback is a mutation), and not implemented.
The shipped representation is `type TxLog = [TxEntry]` (cons-front, first-match
lookup, de-dup at the marshalling boundary). Do not revert to SoA.

**Two lists, not one.** A single `[TxEntry]` list cannot simultaneously represent
the rollback view (`orElse` discards a branch) and the wait-set union (`retry`
keeps every branch's reads). Splitting into `txLog` (rolled back by both `orElse`
and `catchSTM`) + monotone `txWait` (rolled back only by `catchSTM`) removes the
need for `RetryWithWait`, `differenceTxLog`, `tvarInLog`, and mid-flight
`clearRegistrations#`.

**Flat `SApp` spine, not `STMApp`/`STMAppTail`/`ApSingle`/`ApHead`/`ApCons`.**
The earlier draft's free-applicative representation was not implemented. The
shipped AST uses `SApp :: STMPlan (a -> b) -> STMPrim a -> STMPlan b` with the
function accumulated on the left by `planMap`. `planApply` builds this structure.

**`mfix`/`SFix`: explicit black-holing, not a lazy knot.** The lazy `State#`
knot used by the pre-rewrite `MonadFix STM` instance can re-run the effectful
body under lazy black-holing (GHC #15349). `evalFix` uses the `fixIO`/`fixST`
shape instead. The observable difference (a `FixIOException` rather than a true
divergence) is accepted and documented.
