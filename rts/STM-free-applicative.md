# Free applicative STM — design and shipped model

This document describes the representation, semantics, and optimisation
opportunities of the plan-based STM as it ships on the `stm-improvements`
branch. It supersedes earlier drafts that described a mutable structure-of-arrays
log and `STMApp`/`STMAppTail` constructors that were never implemented. See
FINDINGS.md §H-5, M-6 for the audit trail.

## Goals

1. **Deterministic TVar ordering**: address-sorted locking eliminates livelocks
   from incompatible acquisition orders. Achieved in `stmCommitLog#`, which sorts
   the whole log on every commit attempt.
2. **Batch lock/validate/commit**: the whole log is committed in one sorted pass
   by `stmCommitLog#`. This applies to monadic transactions too.
3. **Batch reads for applicative fragments**: `readMany#` reads all `PRead` TVars
   in a fragment in one RTS pass, shrinking the zombie window within that region.
4. **RTS clarity**: the RTS deals only with TVar ownership, wait queues, and log
   arrays; all control flow lives in the Haskell interpreter.

## Representation

`STM a` is a newtype over `STMPlan a`, an executable Haskell AST. `atomically`
interprets the plan against a pair of immutable association lists (the transaction
log and the monotone wait set) and yields one of three outcomes (`STMOutcome`).

```haskell
data STMPlan a where
  SPure     :: a -> STMPlan a
  SPrim     :: STMPrim a -> STMPlan a
  SApp      :: STMPlan (a -> b) -> STMPrim a -> STMPlan b
  SBind     :: STMPlan a -> (a -> STMPlan b) -> STMPlan b
  SRetry    :: STMPlan a
  SOrElse   :: STMPlan a -> STMPlan a -> STMPlan a
  SThrow    :: SomeException -> STMPlan a
  SCatch    :: STMPlan a -> (SomeException -> STMPlan a) -> STMPlan a
  SUnsafeIO :: IO a -> STMPlan a
  SFix      :: (a -> STMPlan a) -> STMPlan a

data STMPrim a where
  PRead    :: TVar a -> STMPrim a
  PWrite   :: TVar a -> a -> STMPrim ()
  PNewTVar :: a -> STMPrim (TVar a)

newtype STM a = STM { stmPlan :: STMPlan a }
```

`Applicative` combination is handled by `planMap` and `planApply`. `planApply`
keeps a maximal pure fragment in `SApp` chains when both operands are
`SPure`/`SPrim`/`SApp`; any other plan shape falls to `SBind`. The flat `SApp`
structure differs from the earlier draft's `STMApp`/`STMAppTail`/`ApSingle`/
`ApHead`/`ApCons` encoding: the shipped form uses a right-spine of `SApp` nodes
with the function accumulated on the left via `planMap (.)`.

## The two-list log model

**Do not implement the mutable structure-of-arrays log** described in earlier
drafts of this document and in `STM-plan.md §3`. The SoA design was rejected
because:

- In-place mutation of traced pointer slots requires nonmoving deletion barriers
  on every resize, sort, rollback, and free-list operation. The critical bugs
  C-1, H-1, H-2, M-1 in FINDINGS.md all trace directly to this fragility.
- Rollback (for `orElse` and `catchSTM`) becomes a heap-mutating operation
  (`pushScope`/`rollbackScope`/shadow entries), which is both more complex and
  more error-prone than the immutable-list alternative.
- The `pushScope`/`rollbackScope`/shadow-entry/`cap`/`len`/`findIndex` machinery
  described in earlier drafts **does not exist** in the source tree.

The shipped model uses **two immutable cons-front association lists**:

### `txLog` — reads and writes

- Type: `[TxEntry]` where `TxEntry :: TVar a -> a -> a -> TxEntry`
  (tvar, expected, new).
- `expected == new` (pointer equality) marks a read-only entry.
- Inserted by consing to the front: O(1), no spine rebuild.
- De-duplicated (first match wins) at the marshalling boundary — the single
  walk that produces the primop arrays.
- Rolled back by **both** `orElse` (discard a branch's reads and writes by
  restoring the captured prior list) and `catchSTM` (same).
- Used only on the `Ok` path: marshalled into `(tvars, expected, new)` arrays
  for `stmCommitLog#`.

### `txWait` — the monotone wait set

- Type: `[WaitEntry]` where `WaitEntry :: TVar a -> a -> WaitEntry`
  (tvar, expected). Reads-only; write-only TVars are never waited on.
- **Monotone**: only ever grows. An `orElse` branch extends it even when that
  branch is discarded (left branch retries → carry `txWait` forward into the
  right branch; the union is implicit in the accumulated list). `catchSTM` rolls
  it back with the body (a caught exception forgets the body's reads).
- Registered exactly once, at the top-level `Retry` in `runAtomically`, via
  `registerLogRange#`. There is no mid-flight registration and no
  `clearRegistrations#` / `RetryWithWait` outcome.
- Used only on the `Retry` path.

The split is why registration can happen at the top: the wait set already carries
the union of every branch's reads, so `runAtomically` need only register it once.
`RetryWithWait`, `differenceTxLog`, and `tvarInLog` are absent from the shipped
code; the monotone `txWait` makes them unnecessary.

### Why not mutable arrays

Linear lookup is irreducible for a heterogeneous `TVar a -> (a,a)` map at this
layer (below `containers`). The O(n²) cost in distinct TVars is real but bounded:
it only bites pathologically large single transactions, which already carry a
ruinous conflict surface. Accepting the O(n²) and using cons-front insert (O(1))
gives a practical constant-factor win over spine-rebuilding append, with zero GC
barrier complexity. If huge transactions become a real bottleneck, add a
*rebuildable* address index that is simply dropped on rollback — never in-place
shadow entries.

## Three-outcome model

```haskell
data STMOutcome a = Ok a | Retry | Raise SomeException
```

There are exactly three outcomes. The earlier draft's four-outcome model (with
`RetryWithWait` as a 4th constructor) is not implemented and is not correct:
mid-flight registration produces the C-3 bug (sibling branches clobber each
other's wait sets). The shipped model returns plain `Retry` from `orElse` branches
and relies on the monotone `txWait` to carry the union.

## Validation (`validate#`)

Reads are taken from live memory at access time. Between two reads, the interpreter
runs arbitrary user code (`SBind` continuations, case scrutinees, `unsafeIOToSTM`
bodies). A transaction that has observed mutually-inconsistent TVars can otherwise:
(a) loop forever, (b) throw a spurious exception that escapes `atomically`, or
(c) run `unsafeIOToSTM` over garbage.

The `validate#` primop performs a lock-free pass over a `(tvars, expected)` array,
checking `expected == current_value` for each entry (pointer equality, no locking).
The Haskell wrapper `validateLog` is called:

1. **Before every `SBind` continuation**: if inconsistent, the continuation is
   abandoned and `Retry` is returned. `runAtomically` re-validates the wait set
   before blocking, so the transaction restarts immediately rather than blocking
   on a stale snapshot.
2. **At the top-level `Retry` in `runAtomically`**, before `registerWaitSet`.

Commit-time validation in `stmCommitLog#` remains the backstop for correctness;
the incremental checks narrow the window in which a zombie transaction can run.

## RTS primops

| Primop | Inputs | Purpose |
|---|---|---|
| `stmCommitLog#` | `tvars`, `expected`, `new`, `len` | Sort by address; lock in order; validate `expected` for all entries; commit writes; unpark waiters for actual updates (`expected ≠ new`); unlock. Returns 0 (success) or 1 (conflict). |
| `registerLogRange#` | `tvars`, `expected`, `start`, `end` | Enqueue the current TSO on each TVar's wait queue for the given range. |
| `blockOnRegistered#` | — | Validate registered TVars; block the TSO until any change; clear registrations on wake. |
| `validate#` | `tvars`, `expected`, `len` | Lock-free pointer-equality check of `expected` against live TVar values. Returns 0 (consistent) or 1 (stale). |
| `readMany#` | `tvars`, `results`, `expected`, `len` | Read all TVars in the array in one pass, filling `results` and `expected`. Returns 0 (ok) or 1 (concurrent commit observed). |

`stmCommitLog#` takes **4** value arguments (no `flags` argument). The earlier
draft's 5-argument form is incorrect (FINDINGS C-5).

## Applicative fragments and static analysis

A *fragment* is any `STMPlan` built solely from `SPure`, `SApp`, and `SPrim` —
no control flow. Within a fragment, the read set is statically enumerable. This
is the precondition for `readMany#` batching.

`fragmentReads` walks the `SApp` spine to collect the read set.

`tryReadMany` is called from `evalSTM` for any `SApp` plan: it fills a `tvars`
array from `fragmentReads`, calls `readMany#`, and if successful folds the batch
into `txLog`/`txWait`. A single-TVar fragment does not trigger `readMany#`
(no benefit from the batch overhead); the threshold is two or more distinct reads.

## `mfix` / `SFix` — settled divergence semantics

`SFix` encodes `mfix` for STM. It uses **explicit black-holing** (the
`fixIO`/`fixST` shape — an MVar + `unsafeDupableInterleaveIO`) rather than a
lazy `State#` knot. This diverges from the description in earlier drafts of this
document that promised "black-hole behaviour" from a lazy knot.

The lazy-knot approach was abandoned for the same reason `fixST` abandoned it
(GHC #15349, Note [fixST]): lazy black-holing can *re-run* the effectful body,
duplicating reads and writes. `evalFix` interprets the body exactly once; the
fixed-point value is placed in an MVar after a successful `Ok`. If the fixed-point
value is forced before the body produces `Ok`:

- On `Retry` or `Raise`, the MVar is never filled. Forcing `ans` blocks
  indefinitely; the runtime detects `BlockedIndefinitelyOnMVar` and re-raises
  it as `FixIOException`.

This preserves the legacy semantic that "forcing the fixed point in a non-`Ok`
body diverges", but via a catchable `FixIOException` rather than a true
blackhole deadlock. The observable difference from a genuine black hole is
limited to code that uses `catch`/`handle` inside `mfixSTM`. This is an accepted,
documented deviation — see the Haddock on `evalFix`. (FINDINGS L-8)

## Handling dynamic information

`SUnsafeIO`, `SCatch`, and `SFix` handle dynamic or effectful operations directly
in the Haskell interpreter. There is no RTS fallback, no plan-compilation phase,
and no `StgSTMPlan` or `stmExecutePlan`.

`unsafeIOToSTM` re-runs on every attempt (commit conflict or retry), preserving
legacy semantics. The `validate#` check before `SBind` continuations means the
IO body is less likely to run over a wildly inconsistent snapshot, but there is
no guarantee.

## Performance notes

- Marshalling to arrays at the primop boundary is unavoidable (Cmm cannot walk a
  Haskell list) but runs once per attempt over only the de-duplicated set.
- `txLogLen` and `txWaitLen` are tracked incrementally as upper bounds (pre-dedup)
  to avoid a separate `length` pass at the marshalling boundary.
- The single-TVar fast paths in `atomically` bypass the interpreter entirely for
  the most common trivial transactions (`PRead`, `PNewTVar`, single `PWrite`).

## Next steps (open)

1. Fix C-1 (watch-queue `NULL` terminator → `END`), H-1/H-2/M-1 (write barriers),
   C-3 (confirmed absent in the shipped two-list + single-registration model —
   verify under the `retryWithWait` removal path), C-4/C-5 (JS codegen).
2. Regenerate `interface-stability` baselines after freezing the primop set.
3. Add orElse wait-union, mfix, async-exception-mid-txn, and conflict-re-run
   tests (FINDINGS H-7, H-8, M-9, M-10).
4. Audit `stm`/`base` structures to maximise transactions in the applicative
   fragment (FINDINGS M-4: `TArray.newArray`).
