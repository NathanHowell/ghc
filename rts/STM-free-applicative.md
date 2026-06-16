# Free applicative STM plan

This note sketches changes to both the `STM` representation and the RTS in order
to exploit a *free applicative* encoding of transactions.  The aim is to make
each transaction expose the set of TVars that it intends to read or write so
that the RTS can schedule work deterministically, acquire locks in a canonical
order, and avoid redundant contention.

## Goals

1. **Deterministic TVar ordering**: two threads running syntactically identical
   STM actions should lock/read the same TVars in the same order, eliminating
   livelocks caused by incompatible lock acquisition orders.
2. **Do the most work possible before executing**: when the plan tells us every
   TVar that will be read or written we can validate those reads once,
   short‑circuit retries earlier, and pre-lock writers in one pass.
3. **Reduce contention**: batching reads and deterministic locking reduces the
   time each thread holds individual TVar locks and prevents cyclic wait
   patterns.
4. **Improve RTS clarity**: isolate the planning/evaluation steps so the core
   STM engine operates on a simple “plan” data structure instead of interpreting
   arbitrary Haskell actions on the fly.

## Representation

STM is represented as an executable Haskell AST (`STMPlan` with `STMApp` for
non-empty applicative fragments). `atomically` interprets the plan against a
GC-managed log and yields `Ok`/`Retry`/`Raise`. The RTS consumes only log arrays
via `stmCommitLog#` and performs batched wait registration using
`registerLogRange#`/`blockOnRegistered#`; there is no RTS `StgSTMPlan` or
plan-compilation step.

## Executable plan semantics

The plan is an executable AST, not just a static TVar list. It evaluates against
a mutable log in Haskell and yields one of three outcomes:

- `Ok a`: commit via `stmCommitLog#` and return `a`.
- `Retry`: register waits on TVars read and call `blockOnRegistered#`.
- `Raise e`: abort and rethrow to IO.

### Log and scopes

- The log is a set of parallel arrays (`tvars`, `expected`, `new`) plus `len`.
  Entries are unique by TVar; pointer equality between `expected` and `new`
  marks a read-only entry.
- `pushScope` captures the current log length (and shadowing state) and
  `rollbackScope` truncates the log back to that point. No TVar writes happen
  during rollback.

### Control flow

- `retry`: registers waits from the log (or from the scope delta) and
  blocks via `blockOnRegistered#`.
- `orElse`: scope before the left branch; on retry register left waits,
  rollback and run the right branch; if both retry, keep registrations from
  both branches.
- `catchSTM`: scope before the body; on exception rollback and run the
  handler. `retry` propagates, matching legacy behavior.

### Unsafe IO

- `unsafeIOToSTM` executes immediately. If the transaction retries or is
  re-executed after a commit conflict, the IO action is re-run, preserving
  legacy semantics.

### Fixpoints (`mfix`)

- `SFix` ties the knot entirely within the STM interpreter. If the fixed-point
  value is forced before the body yields `Ok`, evaluation diverges (black-hole
  behavior), matching the current `MonadFix STM` instance. This is implemented
  with an explicit diverging thunk so non-`Ok` outcomes leave the fixed point
  black-holed. `retry` and exceptions propagate without forcing the fixed-point
  value.

### Applicative fragments

- `SAp` embeds a non-empty applicative fragment (`STMApp` with `ApSingle` or
  `ApHead`/`STMAppTail`). Fragments contain only STM primitives and no control
  flow, which keeps plan extraction deterministic.

## Handling dynamic information

Some STM functions (e.g. `unsafeIOToSTM`, exception handlers, `mfix`) depend on
dynamic information. These are represented directly in `STMPlan` (`SUnsafeIO`,
`SCatch`, `SFix`) and interpreted in Haskell; there is no RTS fallback or
separate plan-compilation phase.

## Contention reduction

- Deterministic locking eliminates cyclic waits.
- Reads avoid locks entirely; they share the same strategy as the current
  “read phase” but know the full read set beforehand.
- Retry/watch handling now queues the thread on all read TVars in one pass,
  meaning fewer lock/unlock cycles.

## Clarity improvements

The RTS core reduces to log-based helpers (`stmCommitLog`, wait registration,
and blocking) that sort, lock, validate, and commit or enqueue waits. Control
flow stays in the Haskell interpreter; the RTS only deals with TVar ownership
and wait queues.

## Next steps

1. Remove remaining plan-era RTS plumbing now that log execution is in place.
2. Add stress tests (randomized concurrent transactions, `orElse` wait-union,
   `unsafeIOToSTM` rerun) to lock in semantics.
3. Audit higher-level STM structures (`TQueue`, `TBQueue`, etc.) to keep
   applicative fragments in `SAp` wherever possible.

This design keeps deterministic ordering, maximizes the amount of work we can do
before committing, and maintains a clear pipeline inside the RTS.

## Prototype status (current branch)

- `GHC.Internal.Conc.Sync` now defines `STMPlan` (SPure/SBind/SAp/SRetry/SOrElse/SThrow/SCatch/SUnsafeIO/SFix) and `STMApp`. `STM` is plan-only; `Applicative` builds `SAp` and `Monad` sequencing uses `SBind`.
- Primitives (`readTVar`, `writeTVar`, `newTVar`, `retry`, `orElse`, `throwSTM`, `catchSTM`, `unsafeIOToSTM`) emit `STMPlan` nodes directly; dynamic IO remains expressible via `SUnsafeIO`.
- `atomically` runs the Haskell interpreter over `STMPlan`, logging TVar access into `TxLog` arrays and using scopes for `orElse`/`catchSTM`. Waits are registered in batched ranges; there are no wait-set arrays.
- The RTS fast path now consumes the log arrays via `stmCommitLog#` and uses `registerLogRange#`/`blockOnRegistered#` for waiting, sorting TVars by address on each attempt and performing lock/validate/commit or wait. Pointer-equal `expected == new` suppresses wakeups and update counters.

The immediate follow-up is to audit `stm`/`base` data structures so more transactions stay in the applicative fragment and hit the log-based executor, and to continue trimming residual plan-era plumbing where it no longer adds value.

## Implementation plan (executable plan + Haskell log)

This section is the authoritative, step-by-step plan for the executable STM
plan and Haskell log executor. It is intended to be complete and precise for
implementation by a runtime/compiler engineer.

### Constraints and invariants

- Do not add fields to `StgTVar` (no stable `tvar_id`). Lock ordering therefore
  re-sorts by TVar address on every attempt.
- The STM log is GC-managed; no manual RTS allocation for log/plan structures.
- Keep legacy semantics for `retry`, `orElse`, `catchSTM`, and `unsafeIOToSTM`
  (IO is re-run on retry or commit conflict).
- No nested `atomically` inside `STM`; any internal scope/checkpoint is an
  implementation detail and is not user-visible.
- `expected == new` (pointer equality) means "non-update" and must not wake
  waiters or increment update counters, matching current RTS behavior.

### 1. Haskell AST representation

Define an explicit executable AST in `libraries/ghc-internal/src/GHC/Internal/Conc/Sync.hs`:

```haskell
data STMPlan a
  = SPure a
  | SBind (STMPlan a) (a -> STMPlan b)
  | SAp (STMApp a)
  | SRetry
  | SOrElse (STMPlan a) (STMPlan a)
  | SThrow SomeException
  | SCatch (STMPlan a) (SomeException -> STMPlan a)
  | SUnsafeIO (IO a)
  | SFix (a -> STMPlan a)

data STMPrim a
  = PRead (TVar a)
  | PWrite (TVar a) a
  | PNewTVar a

data STMApp a where
  ApSingle :: STMPrim a -> STMApp a
  ApHead   :: STMPrim x -> STMAppTail (x -> a) -> STMApp a

data STMAppTail a where
  ApNil  :: a -> STMAppTail a
  ApCons :: STMPrim x -> STMAppTail (x -> a) -> STMAppTail a
```

Key points:
- `STMPlan` handles control flow; `STMApp` is non-empty and contains only
  primitives.
- `SPure` is the only "pure" node; applicative fragments are always effectful.
- `ApSingle` avoids `ApNil id` for the common single-primitive case.
- `SFix` encodes `mfix` by tying a lazy knot inside the transaction, matching
  the existing `MonadFix STM` semantics via the interpreter-level knot.
  The body runs in the same STM attempt and therefore sees uncommitted log
  entries, not just committed TVar state. The interpreter evaluates the body
  once and only forces the fixed-point value if the body returns `Ok`. If the
  body retries or raises, the fixed-point value is left unevaluated and only
  diverges if demanded. `SFix` is re-evaluated on each attempt; it must not use
  `readTVarIO#`/`unsafePerformIO` to read committed state.

### 2. STM instances and builder rules

Implement `Applicative` and `Monad` for `STMPlan`/`STM` so that ApplicativeDo
builds `SAp` fragments:

- `pure = SPure`
- `(<*>)` combines `STMApp` fragments when both operands are `SPure`/`SAp`;
  otherwise, fall back to `SBind` to preserve semantics in mixed control flow.
- `>>=` always uses `SBind`.
- `readTVar`/`writeTVar`/`newTVar` produce `SAp (ApSingle ...)`.
- `throwSTM` produces `SThrow`, `retry` produces `SRetry`, `orElse` produces
  `SOrElse`, `catchSTM` produces `SCatch`, `unsafeIOToSTM` produces `SUnsafeIO` and binds with `SBind` when its result is used.
- `mfix` produces `SFix` to preserve the legacy knot-tying semantics.

Applicative combination details:
- Treat `ApSingle p` as `ApHead p (ApNil id)` when composing.
- Use the standard free-applicative rule to avoid extra allocations:
  `ApHead f ft <*> ApHead x xt` becomes `ApHead f (apTail ft (ApHead x xt))`.
- Keep all loops strict; avoid building intermediate lists.

### 3. Haskell log layout and operations

Implement a GC-managed log with structure-of-arrays:

```haskell
data TxLog = TxLog
  { tvarsVar    :: MutVar# RealWorld (SmallMutableArray# RealWorld Any)
  , expectedVar :: MutVar# RealWorld (SmallMutableArray# RealWorld Any)
  , newVar      :: MutVar# RealWorld (SmallMutableArray# RealWorld Any)
  , shadowedVar :: MutVar# RealWorld Int
  , meta        :: MutableByteArray# RealWorld -- len, cap
  }
```

Rules and invariants:
- Entries are unique by TVar. `findIndex` scans linearly from `len-1` down.
- `expected` is read once, at first access.
- `new` always holds the value read or last written; `expected == new` implies
  a read-only entry.

Operations (all strict, `Int#`-based, unboxed tuples):
- `newTxLog` allocates arrays with initial capacity (e.g. 8).
- `resetTxLog` sets `len=0`, `shadowed=0`; arrays are reused.
- `pushScope` captures the current `len` and `shadowed` state.
- `rollbackScope` restores those lengths and truncates the log; no TVar writes
  are performed.
- `readTVarLog`:
  - If entry exists, return `new`.
  - Else read current value, append entry with `expected = new`.
- `writeTVarLog`:
  - If entry exists and predates the current scope, append a shadow entry so
    rollback can discard it by truncation; logs are compacted before commit if
    any scopes were used.
  - If entry exists and is within the scope, update `new` in place.
  - Else read current value for `expected`, append entry, set `new`.

### 4. Scope stack and registrations

Scopes are internal only (not exposed to users):
- `pushScope` captures log length for `orElse` and `catchSTM`.
- `rollbackScope` truncates the log and restores the previous shadowed state.

Wait registration:
- `retry` registers waits on all `tvars[0..len)`.
- For `orElse`, register waits from entries added since scope, rollback,
  then register waits from the right branch; if both retry, registrations are
  kept for both branches (duplicates ignored by pointer equality).
- Empty registration blocks forever but remains interruptible (legacy behavior).

### 5. Interpreter and outcomes

Define a strict interpreter:

```haskell
data STMOutcome a = Ok a | Retry | Raise SomeException
```

Evaluation rules:
- `SAp` runs the applicative fragment, updates log, yields a value.
- `SBind` evaluates left then applies continuation.
- `SRetry` yields `Retry`.
- `SOrElse` uses scopes; on left retry, rollback and run right; if both
  retry, register waits from both branches.
- `SCatch` uses scopes; on exception, rollback and run handler; `retry`
  propagates.
- `SUnsafeIO` executes immediately and re-runs on retry/commit conflict.
- `SFix` ties the knot inside the transaction. If the fixed-point value is
  forced before the body produces `Ok`, evaluation diverges just as in the
  legacy `mfix` implementation.

Execution loop for `atomically`:
- Create/clear log.
- Interpret AST to `STMOutcome`.
- On `Ok`, call `stmCommitLog#`; on conflict, reset log and re-run AST.
- On `Retry`, register waits from the log, call `blockOnRegistered#`, and re-run.
- On `Raise`, throw to IO.

### 6. RTS primops and boundary

Add these primops:
- `stmCommitLog#`:
  - Inputs: log arrays (`tvars`, `expected`, `new`) and `len`.
  - RTS sorts by TVar address on each attempt, permuting all arrays together.
  - Locks in order, validates `expected` for all entries (read-only and write),
    commits writes, unparks waiters for actual updates, unlocks.
  - Returns `0` success or `1` conflict.
- `registerLogRange#`:
  - Inputs: log arrays plus start/end indices.
  - Enqueues the current TSO on each TVar wait queue in the given range and
    records the registrations (deduplicated per TVar).
- `blockOnRegistered#`:
  - Validates registered TVars, blocks the TSO until any changes, and clears
    registrations on wake.
- `clearRegistrations#`:
  - Removes the current TSO from all registered TVar wait queues.

Implementation notes:
- Keep current lock/unlock primitives and memory ordering.
- Reads and writes are validated using pointer equality; no value forcing.
- No new fields on TVars; sorting happens on each attempt due to moving GC.

### 7. Thread state and GC

- The log and AST are ordinary Haskell closures, kept alive across retries.
- The TSO or `atomically` loop must retain the log and AST across `blockOnRegistered#`.
- RTS uses only the TRec header to track ownership/locking state; no
  `TRecEntry` allocations in the fast path.
- Scavenger must trace any log or plan references stored in the TSO.

### 8. Semantics parity checklist

- `retry` is not caught by `catchSTM`.
- `orElse` retries the right branch when the left retries; both retry keeps
  registrations from both branches.
- `unsafeIOToSTM` re-runs on retry and on commit conflict.
- `writeTVar` of a pointer-equal value must not wake waiters or increment update
  counters.
- `throwSTM` propagates to IO when uncaught.

### 9. Migration steps

1. Introduce the AST and builder rules in `GHC.Internal.Conc.Sync`.
2. Implement the log and interpreter; route `atomically` through the interpreter.
3. Add `stmCommitLog#` plus `registerLogRange#`/`blockOnRegistered#`/`clearRegistrations#`,
   update Cmm/RTS glue, and switch commit/wait to use the log arrays.
4. Remove dependency on legacy `TRecEntry` paths in the fast path; keep only
   header ownership for now.
5. Audit remaining STM operations (`readTVarIO`, `modifyTVar'`, queues) to keep
   applicative fragments in `SAp` where possible.
6. Remove legacy interpreter path once all semantics are covered by the new
   executor.

### 10. Tests and validation (stress-oriented)

- Add randomized concurrent tests under `testsuite/tests/stm/`:
  - Multiple threads perform random transactions over a shared TVar array.
  - Invariants checked at end (e.g. sum of counters equals total increments).
  - Seeded RNG for reproducibility.
- `unsafeIOToSTM` re-run test: count IO side effects across retries.
- `orElse` wait-set test: left waits on A, right waits on B, ensure union.
- Run with `-threaded -with-rtsopts "-N4"` and timeouts.
- Add one lock-ordering contention test to ensure deterministic acquisition.
