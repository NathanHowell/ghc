# Plan to address STM findings

## Runtime fixes

- [ ] Add write barriers when pushing/popping STM freelist entries (`StgTVarWatchQueue`, `StgTRecHeader`). Ensure both allocation and free paths use `dirty_*` or equivalent so non-moving GC sees the links.
- [ ] Adjust `cond_lock_tvar` so `updateRemembSetPushClosure` only runs when the CAS succeeds (`result == expected`). Consider also pushing the previous `current_value` when we actually overwrite it in `lock_tvar` to keep consistency.
- [x] Remove the stale `stmValidateNestOfTransactions` note; validation now lives in the log commit/wait paths.

## STM library cleanups

- [ ] Re-implement `tryPeekTQueue`, `tryPeekTBQueue`, and `tryPeekTChan` to avoid the `tryRead`/`unGet` dance. Instead, mirror the blocking `peek` but wrap it in `orElse (return Nothing)` so successful peeks only read TVars.
- [ ] Investigate and adopt alternative queue representations (e.g. difference lists, `Seq`, or two-list FIFO with back stored in queue order) so `read`/`peek` no longer reverse the writer list while holding STM locks. Benchmark to ensure throughput remains acceptable.

## RTS/library integration ideas

- [ ] Prototype multi-TVar STM primitives (e.g. `stmReadMany#`, `stmWriteMany#`) and surface them via new `STM` helper functions (`readTVar2`, `writeTVar2`, etc.). Update core library structures (`TQueue`, `TBQueue`, `TChan`) to use the new primitives so the RTS can lock/validate the involved TVars together.
- [ ] Explore representing STM transactions as a deferred applicative tree or other declarative form so the RTS can analyse the read/write set before execution. This requires design work (new `STM` constructors, scheduler changes, codegen updates). Draft a proposal outlining trade-offs and migration path.
- [ ] Audit remaining STM library APIs for redundant read–write sequences (e.g. `stateTVar`, `modifyTVar'`) and document patterns that minimise TVar updates. Encourage users via `base` docs to structure transactions so pure reads are separated from writes when possible.
- [x] Track the `funArgTy` compiler panic triggered by the new applicative metadata. Refactoring `STM` into a thin wrapper around `STMPlan` removed the problematic levity-polymorphic worker so both `GHC.Internal.Conc.Sync` and `GHC.Internal.Conc.STMPlan` now build at `-O2` without panic; keep monitoring future refactors for regressions.

## Applicative planner prototype (obsolete)

This section is superseded by the executable-plan + Haskell log design in
`rts/STM-free-applicative.md`. The RTS no longer uses `StgSTMPlan` or
`stmExecutePlan`.
