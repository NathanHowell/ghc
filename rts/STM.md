# Notes on `rts/STM.{h,c}` and STM library integration

This document captures observations from reviewing the runtime STM implementation
and the higher-level `Control.Concurrent.STM` library. It reflects the shipped
state of the `stm-improvements` branch. See `rts/STM-free-applicative.md` for the
full design rationale.

## Runtime STM implementation

### Write barriers on capability freelists

`rts/STM.c` keeps capability-local free lists for `StgTVarWatchQueue` and
`StgTRecHeader`. These lists are manipulated without write barriers even though
the objects may contain pointers. In a non-moving GC build, the freelists
themselves live in `Capability`, so GC only sees them if we record the `next`
pointers with the appropriate barrier. Without it the collector can reclaim
descriptors that remain reachable through a freelist entry, leading to
use-after-free when the freelist is later reused.

### `cond_lock_tvar` and the remembered set

In the fine-grained locking path (`STM_FG_LOCKS`), `cond_lock_tvar`
unconditionally calls `updateRemembSetPushClosure(cap, expected)` whenever the
CAS returns anything non-null. Under contention the CAS often fails, but we still
push `expected` into the remembered set even though the TVar still points at that
closure. This can pin dead closures and unnecessarily grow the remembered set. The
push should be gated on `result == expected` so it only runs when the TVar
actually starts pointing to the TRec. This fix is already applied on this branch.

### Validation

The old `stmValidateNestOfTransactions` path no longer exists in the log-based
RTS. Validation is handled by `stmCommitLog#` at commit time and, for incremental
mid-flight validation, by the `validate#` primop. The Haskell interpreter calls
`validateTx` (which invokes `validate#` over `txReads`) before
potentially-divergent `SBind` continuations and at the top-level `Retry` path in
`runAtomically`. This is the mechanism that prevents "zombie transactions" — a
transaction that has read a mutually-inconsistent snapshot cannot loop forever or
throw spurious exceptions, because the mismatch is detected before the continuation
runs, and the transaction is restarted immediately.

If a separate pessimistic validation path is reintroduced in future, avoid locking
read-only TVars; prefer the commit-style version checks for readers.

### Watch-queue GC terminator

`StgTVarWatchQueue` is a `MUT_PRIM` closure. Every pointer field in a `MUT_PRIM`
is evacuated by the generic scavenger without null guards. The per-thread wait
list (`trec->wait_queue`) must therefore be terminated with
`stg_END_STM_WATCH_QUEUE_closure`, never `NULL`. All `q != NULL` guards in the
C source must compare against `END` instead.

### `tryPeek` helpers

`tryPeekTQueue`, `tryPeekTBQueue`, and `tryPeekTChan` (in the `stm` submodule)
have been re-implemented to avoid the `tryRead`/`unGet` round-trip. They now
mirror the blocking `peek` variant wrapped in `orElse (return Nothing)`, so a
successful peek only reads TVars and produces no spurious writes. This is already
applied on this branch.

### Queue representations

Functions like `readTQueue`, `readTBQueue`, and their `peek` variants reverse the
`write` list when the `read` side is empty. Choosing a data structure that supports
amortised O(1) pop from the back would make these transactions shorter and reduce
lock hold times.

## Applicative information and RTS visibility

### What `Applicative` buys (and does not buy)

`STM` is now an executable AST (`STMPlan`). `Applicative` combination builds
`SApp` nodes via `planApply`; `Monad` sequencing uses `SBind`. The read set of a
pure applicative fragment (built solely from `SPure`/`SApp`/`SPrim`) is statically
enumerable, which enables **`readMany#` batching**: batch-read all `PRead` TVars
in one RTS pass, shrinking the window in which the transaction can observe an
inconsistent snapshot (the reads are effectively simultaneous).

The batch capability for commit and wait registration, however, comes from the log
rather than from `SApp` specifically: `stmCommitLog#` sorts the *entire* log by
address and locks/validates/commits the whole set in one pass; `registerLogRange#`
does the same for the wait set. This holds for monadic transactions too.

A pure `f <$> readTVar a <*> readTVar b` may be evaluated via `readMany#` (batch
path in `tryReadMany`); the same transaction written as a `do`-block goes through
`SBind` and one TVar at a time. The applicative form is preferable where practical.

### Potential extensions

1. **`readMany#`** — already wired as a primop and called by `tryReadMany`; further
   reducing the zombie window within fragments.

## Free applicative prototype status

`GHC.Internal.Conc.STM` defines `STMPlan` with constructors
`SPure`/`SPrim`/`SApp`/`SBind`/`SRetry`/`SOrElse`/`SThrow`/`SCatch`/`SUnsafeIO`/`SFix`.
`STM` is a newtype over `STMPlan`.

Primitives (`readTVar`, `writeTVar`, `newTVar`) produce `SPrim` nodes;
`Applicative` builds `SApp` chains via `planApply`; control constructs use their
dedicated nodes. `atomically` dispatches through a fast path for single-primitive
transactions, then falls back to `runAtomically` which drives the full interpreter.

The RTS fast path consumes the log arrays via `stmCommitLog#` and registers waits
using `registerLogRange#`/`blockOnRegistered#`, sorting TVars by address on each
attempt and performing lock/validate/commit or wait. Pointer-equal `expected == new`
suppresses wakeups and update counters.

The `funArgTy` compiler panic triggered by earlier designs is resolved: `STM`
exposes no levity-polymorphic fields and `GHC.Internal.Conc.STM` builds at `-O2`
without workaround pragmas.
