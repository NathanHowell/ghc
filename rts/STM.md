# Notes on `rts/STM.{h,c}` and STM library integration

This document captures observations from reviewing the runtime STM implementation and the higher-level `Control.Concurrent.STM` library. It includes correctness concerns, performance opportunities, and places where the RTS may be extended to better exploit information from the library layer.

## Runtime STM implementation

### Missing write barriers on capability freelists

`rts/STM.c` keeps capability-local free lists for `StgTVarWatchQueue` and `StgTRecHeader`. These lists are manipulated without write barriers even though the objects may contain pointers. In a non-moving GC build, the freelists themselves live in `Capability`, so GC only sees them if we record the `next` pointers with the appropriate barrier. Without it the collector can reclaim descriptors that remain reachable through a freelist entry, leading to use-after-free when the freelist is later reused.

### `cond_lock_tvar` leaks closures into the remembered set

In the fine-grained locking path (`STM_FG_LOCKS`), `cond_lock_tvar` unconditionally calls `updateRemembSetPushClosure(cap, expected)` whenever the CAS returns anything non-null. Under contention the CAS often fails, but we still push `expected` into the remembered set even though the TVar still points at that closure. This can pin dead closures and unnecessarily grow the remembered set. We should gate the push on `result == expected` so it only runs when the TVar actually starts pointing to the TRec.

### Legacy pessimistic validation note (obsolete)

The old `stmValidateNestOfTransactions` path no longer exists in the log-based
RTS; validation is handled by `stmCommitLog` and wait registration uses
`registerLogRange#`/`blockOnRegistered#` with the configured read-phase strategy. If
a separate pessimistic validation path is reintroduced, avoid locking read-only
TVars; prefer the commit-style version checks for readers.

### `tryPeek` helpers perform read+write roundtrips

`Control/Concurrent/STM/TQueue.hs:143-150`, `Control/Concurrent/STM/TBQueue.hs:187-194`, and `Control/Concurrent/STM/TChan.hs:166-173` implement `tryPeek…` by calling `tryRead…` followed by `unGet…`. On success this performs an update to each TVar touched by the read even though a pure peek needs only reads. These redundant writes increase the amount of work the RTS must do (extra TRec entries, more dirtying) and exacerbate contention. Re-implementing each `tryPeek…` like its blocking `peek…` sibling, wrapped in `orElse (return Nothing)`, would avoid the writes entirely.

### Queue implementations reverse their write lists inside a transaction

Functions like `readTQueue`, `readTBQueue`, and their `peek` variants reverse the `write` list when the `read` side is empty. Even though the reverse is carefully lazy, we still need to traverse the list while all the relevant TVars are locked. Choosing a data structure that supports amortised `O(1)` pop from the back (e.g. a difference list, `Seq`, or two-list representation that keeps `write` in FIFO order) would make these transactions shorter and reduce lock hold times.

## Applicative information and RTS visibility

### Current `Applicative STM` is purely syntactic sugar

`Control/Monad/STM.hs:88-94` defines the `Applicative` instance as `pure = return; (<*>) = ap`. Even if library code rewrites to `<$>`/`<*>` instead of `do`-notation, the RTS still executes each `STM` action sequentially, invoking `stmReadTVar`/`stmWriteTVar` as soon as it sees them. Therefore the runtime never has visibility into a “batch” of TVars that could be validated or locked together. Exploiting applicative structure would require a different representation (e.g. a free applicative that records the TVar set until `atomically` runs) or new RTS primitives that operate on multiple TVars at once. Without such changes, simply adopting applicative syntax does not affect locking.

### Potential extensions

1. **Multi-read/write primitives:** We could add RTS entry points like `stmReadTVar2#`, `stmReadTVar3#`, or a vector-based `stmReadMany#`. Library code (e.g. `TQueue`, `TBQueue`, `TChan`) already knows which TVars it will touch per operation. Calling these multi-operations would let the RTS lock each TVar once, check versions in one pass, and queue the waiting thread on all TVars atomically.
2. **Declarative STM program representation:** Instead of interpreting STM actions immediately, we might store them as an applicative tree of primitive operations, allowing the scheduler to analyse the whole set of reads/writes before executing. This is a significant redesign and would require a new API surface.
3. **Better RTS–library contracts:** Shorter transactions (e.g. by removing redundant writes and expensive list reversals) naturally reduce lock contention. Likewise, library functions that currently perform read–modify–write sequences could be refactored to separate pure reads from updates so that validation work is minimised.

### Summary

To “see more variable access at a time” the RTS needs either explicit hints (multi-variable primitives) or a deferred, declarative representation of STM actions. Applicative syntax alone cannot provide that. In the meantime, reducing redundant writes and shortening the critical sections in the STM library will give the runtime more headroom.

## Free applicative prototype progress

- `GHC/Internal/Conc/Sync.hs` now models STM as a `STMPlan` AST plus a free applicative `STMApp`. The `STM` value carries both the runnable closure and the plan, and `atomically` interprets the plan while logging TVar access in `TxLog` arrays.
- Primitives (`readTVar`, `writeTVar`, `newTVar`) build `STMPrim` nodes inside `SAp`. Control constructs use `SRetry`, `SOrElse`, `SThrow`, `SCatch`, `SUnsafeIO`, and `SFix`. Applicative execution uses `SAp` and `Monad` sequencing uses `SBind`.
- The RTS fast path now consumes the log arrays via `stmCommitLog#` and registers waits using `registerLogRange#`/`blockOnRegistered#` (no wait arrays), performing lock/validate/commit or wait without `StgSTMPlan` attachment. Pointer-equal `expected == new` suppresses wakeups and update counters.

These changes establish a concrete bridge between library code and the RTS: the library can now mark plan-friendly transactions, and the runtime executes them without reinterpreting the transaction record. Future work focuses on richer plans (expected values, retry metadata) and pushing more of `stm`/`base` into the applicative fragment so the new executor can take effect more often.

### Compiler status

The original `STM` datatype stored the runnable closure and applicative metadata side-by-side, which kept triggering the long-standing `funArgTy` panic when compiling concurrency modules with profiling enabled. The current thin-wrapper design sidesteps the issue entirely: the runnable closure lives inside `STMPlan`, and `STM` exposes no levity-polymorphic fields, so `GHC.Internal.Conc.Sync` and `GHC.Internal.Conc.STMPlan` both build at `-O2` without any module-level pragmas. We removed the temporary `-O0` hacks from `Stack.CloneStack`, `Conc.Signal`, `Conc.Bound`, `IO.Handle.Internals`, and `Event.Poll` after verifying that `stage1:lib:ghc-internal` builds cleanly. Future regressions should be addressed in the compiler proper rather than reintroducing the workaround.
