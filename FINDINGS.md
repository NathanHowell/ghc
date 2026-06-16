# STM rewrite — review findings

**Branch:** `stm-improvements` (merge-base `master` @ `b6faf5d04c`)
**Scope:** the full STM rewrite across `ghc-internal` (Haskell interpreter), the RTS (C/Cmm), the
JS backend, the compiler primop plumbing, **and the `libraries/stm` submodule** (its own
`stm-improvements` branch).
**Method:** read-only, multi-agent review — 8 per-subsystem finders → independent adversarial
verification of every finding (re-read the cited code, tried to refute) → cross-layer synthesis.
60 agents total. Findings below are only those that **survived** verification, with verdicts noted.
**This review touched no source files.**

---

## TL;DR — why it doesn't work yet

Five independent, load-bearing defects. Any one of the first three alone is enough to make STM
unusable:

1. **It crashes under GC.** A *live* `StgTVarWatchQueue` now carries a `NULL` pointer field, and the
   generic `MUT_PRIM` scavenger has no `NULL` guard. Essentially every retrying/blocking transaction
   segfaults (release major GC) or asserts (DEBUG) the first time GC scavenges the blocked thread.
   → C-1.
2. **Zombie transactions.** Reads are taken from live memory with **no incremental validation** — a
   transaction that has observed mutually-inconsistent `TVar`s can loop forever, throw a *spurious*
   exception that escapes `atomically`, or run `unsafeIOToSTM` over impossible state. Classic GHC's
   defense (scheduler-driven abort of inconsistent transactions) was removed and nothing replaced it.
   → C-2.
3. **The JS backend can't build.** `genPrim` is a total case: `registerLogRange#` has no handler and
   `stmCommitLog#` binds a phantom 5th arg. No STM runs on JS. → C-4, C-5.
4. **`orElse` + `catchSTM` lose wakeups.** Wait registration is a single per-TSO list cleared
   globally; a handler that raises mid-flight wipes a sibling branch's registration → the thread
   blocks on an incomplete wait set and never wakes. → C-3.
5. **The testsuite is wired to fail.** `interface-stability` baselines are stale vs. the new primop
   set and the new `STM` representation; orphaned `.stdout` files remain after test deletions. → H-6, H-7, M-9.

On performance: the transaction log is an immutable association list (`type TxLog = [TxEntry]`), so
every transaction is **O(n²)** in the number of distinct `TVar`s touched, with 2–3 fresh array
allocations + full copies per commit/retry. This is real but bounded — it only bites pathologically
large single transactions (thousands of TVars), not the small transactions STM is designed for. The
list is the **right** representation and should stay; see "The elegant target" for why mutable arrays
are the wrong trade. → H-3, H-4.

The good news: the RTS commit path itself (sort → lock → validate → commit) is internally sound, the
`expected == new` no-wakeup suppression is correct, the `cond_lock_tvar` remembered-set fix landed,
the `tryPeek` and `MonadFix` submodule changes are clean, and the immutable-list model is the *more
elegant* target — its only real flaw is that one list is overloaded with two jobs (rollback view +
wait-set union), which is fixable without abandoning immutability.

---

## Root causes (synthesis)

1. **No read-set validation primitive.** The interpreter only ever validates at commit
   (`stmCommitLog#`) and at block (`blockOnRegistered#`). There is no `validate#` over the log, so a
   transaction running arbitrary Haskell between reads can never be aborted when its snapshot goes
   inconsistent. This single missing mechanism is the root of both the zombie-transaction critical
   **and** the inability to maintain a correct `orElse` wait-union.

2. **The watch-queue list is `NULL`-terminated instead of using `stg_END_STM_WATCH_QUEUE_closure`.**
   The new per-thread registration list (`trec->plan` → `next_tso_queue_entry`) breaks the invariant
   that scavenged `MUT_PRIM` pointer fields are never `NULL`. Crashes every blocking transaction
   under GC.

3. **Registration scoping is ad-hoc.** A single per-TSO wait list + a *global* `clearRegistrations#`
   + an undocumented 4th outcome `RetryWithWait` that splits "who registers" between `orElse`
   branches and the top loop. Composes into lost/spurious wakeups under nesting.

4. **The log is overloaded with two conflicting jobs.** A single `[TxEntry]` list serves both the
   *rollback view* (commit must discard an `orElse` branch's reads+writes) and the *wait-set union*
   (`retry` must remember every branch's reads). Conflating them forces eager, mid-flight, per-branch
   wait registration + the global clear + `RetryWithWait` — the tangled, buggy part (root cause 3).
   The list itself is fine; splitting the two roles is the fix. (The O(n²) cost is a separate, bounded
   perf issue — H-3/H-4 — not a reason to change the representation.)

5. **The JS backend and test baselines were never re-derived against the final primop set.** Dead ops
   (`registerWait#`, `h$stmWait`) coexist with a missing live op (`registerLogRange#`); `.stdout`
   snapshots predate the primop changes.

---

## The elegant target (recommendation)

**Keep the immutable `[TxEntry]` list — do *not* adopt the docs' mutable structure-of-arrays log.**
The SoA design is fragile, and it is the direct source of half the GC criticals here: the in-place
mutation of traced pointer slots behind C-1, H-1, H-2, M-1 all stem from mutating arrays + capacity
growth + shadow entries. Immutable cons cells are write-once, so they need **no** nonmoving deletion
barriers, and rollback falls out for free (`orElse`/`catchSTM` just hand the alternative the captured
prior `log` value — no `pushScope`/`rollbackScope`/shadow entries to get wrong). At this layer (below
`containers`) a heterogeneous `TVar a → (a,a)` map *must* be an existential + `unsafeCoerce#`; that is
inherent, and the list keeps it localized.

The list's only structural flaw is that it does two jobs at once. **Split them:**

- **`log`** (reads + writes) — rolled back by *both* `orElse` and `catchSTM`; used only on the `Ok`
  path (validate/commit).
- **`waitSet`** (reads only) — **monotone**: extended by an `orElse` branch even when that branch is
  discarded, but rolled back by `catchSTM` (a caught exception forgets the body). Used only on the
  `Retry` path.

Two lists are genuinely needed because `waitSet ⊋ log`'s reads: in
`x <- readTVar a; (readTVar b >> retry) orElse (readTVar c >> retry)`, a full retry must wait on
**a, b, c**, but commit-rollback must keep only **a**. One list cannot represent both without the
eager-registration hack that creates C-3.

With the split, the whole registration tangle collapses:

- **Registration happens exactly once**, in `runAtomically` on top-level `Retry`, over the entire
  `waitSet`. `RetryWithWait` is **deleted** (H-6); `differenceTxLog`/`tvarInLog` are **deleted** (L-3);
  the mid-flight `clearRegistrations#` churn is gone and **C-3 vanishes structurally** — nothing can
  clobber a sibling's registration if nothing registers until the end.
- `waitSet` is reads-only, so write-only TVars are no longer registered as waiters (kills the
  spurious-wakeup nit).

Two further pieces are orthogonal to the log type and still required:

- **Validation:** add one lock-free `validate#` over the read set and call it before any
  potentially-divergent continuation and at the top-level `Retry`. This is the only correctness
  mechanism STM fundamentally needs beyond commit, and it is what fixes the zombie-transaction critical
  (C-2). A cheap interim is an O(n) re-check of logged read-only entries inside `readTVarTx`.
- **GC:** terminate the per-thread wait list with `stg_END_STM_WATCH_QUEUE_closure` (never `NULL`);
  switch every `q != NULL` guard to compare against `END`; stop zeroing pointer fields in
  `free_stg_tvar_watch_queue` (the freelist is dropped wholesale by `stmPreGCHook`). Rename
  `trec->plan` → `wait_queue`.

**Smaller cleanups that keep the list immutable:** switch insert to **cons-front + first-match
`lookup`** (insert becomes `entry : log` — O(1), no spine rebuild, far less GC churn — deletes
`insertTxLog`; dedup is deferred to the commit marshalling pass). This removes the allocation churn and
a 2× constant but **not** the O(n²) — linear lookup is irreducible here. Reuse the file's own
`Eq (TVar a)` pointer-eq idiom for `sameTVar` and confine the value `unsafeCoerce#` to a single
accessor.

**On O(n²):** it is inherent to any linear structure and cannot be removed cleanly without `containers`
or a mutable index. It only bites pathologically large transactions, which already carry a ruinous
conflict surface — so accept it, document the limit, and do **not** trade it for the fragility of
mutation. If huge transactions ever genuinely matter, add a *rebuildable* address index that is simply
dropped on rollback (so rollback stays free), never in-place shadow entries.

---

## What the `Applicative`/`Alternative` structure does and doesn't buy

The headline motivation for the rewrite was to "let the RTS lock/validate many TVars at once" via a
free-applicative encoding. It's worth being precise about what survives, because it's easy to assume
the batching comes from `Applicative` when it does not.

**The batch capability is real and preserved — but it comes from the log, not from `Applicative`.**
At commit, `commitTxLog` marshals the *entire* accumulated log into arrays and `stmCommitLog#` sorts by
address and locks → validates → commits → unparks the whole set in one pass; `registerLogRange#` does
the same for the wait set. This holds for **monadic** transactions too, and is independent of the
immutable-list / two-list change. So we keep:

| Capability | Status | Source |
|---|---|---|
| Batch lock/validate/commit of the whole read+write set | ✅ preserved | log + `stmCommitLog#` |
| Deterministic address-ordered locking (no lock-order livelock) | ✅ preserved | sort in commit |
| Batch wait-registration on the union | ✅ preserved | `registerLogRange#` + monotone `waitSet` |
| Pre-execution batch **reads** of a statically-known set | ❌ not realized today | would need `readMany#` |

**`Applicative` is, at runtime, still effectively syntactic.** Although `<*>` builds `SApp` nodes
(`planApply`, `Conc/STM.hs:95-100`), the interpreter runs them one TVar at a time:
`evalSTM (SApp pf px)` evaluates `pf` then `evalPrim px` → `readTVarTx` → `readTVarIO` — a single read,
at access time, exactly like the `SBind` path. There is no `readMany#` and nothing consumes a
fragment's read set as a batch, so `f <$> readTVar a <*> readTVar b` behaves identically to the
equivalent `do`-block. (`rts/STM.md` itself describes the pre-rewrite "Applicative is syntactic sugar"
state; the rewrite started *building* `SApp` but never built the machinery to *exploit* it.)

**`Alternative` (`orElse`/`<|>`) is not "lock many at once"** — it is the retry/wait-union, handled by
the monotone reads-only `waitSet`: compose alternatives, wake on the union of both branches' reads.
Preserved.

**The latent value of `SApp` (the design fork).** An `SApp` fragment is exactly the region where the
read set is statically enumerable *and* free of intervening control flow. That makes it the right hook
to add a real `readMany#` later — which would (a) deliver the original "read/validate many at once"
goal and (b) shrink the **C-2 zombie window**, since nothing can diverge or throw between batched
reads. This is orthogonal to the immutable-list / two-list design. The honest alternative: if we do
**not** intend to add batch reads, `SApp` currently earns its keep only as a marker for that future
optimization and as a demarcation of side-effect-free read regions; it could be folded into `SBind` to
simplify, at the cost of giving up that option. Decide explicitly rather than leaving `SApp` as
unexploited structure.

---

## Performance opportunities (fragment-only): batch reads + eager write-locking

These are the **unrealized second half** of the original applicative design (`STM-free-applicative.md`
Goals #1–2: deterministic ordering + "do the most work before executing / pre-lock writers in one
pass"). Both are enabled by the one property an `SApp` fragment guarantees that a monadic block does
not: **the read/write set — and write *targets* — are statically known, with no control flow between
nodes.** Outside a fragment, `x <- readTVar a; writeTVar (if x then b else c) v` makes the set
value-dependent, so neither is safe. Both are orthogonal to the log representation and the two-list
design, and both are **semantics-preserving** (pure contention/latency policy — STM promises no
fairness or serialization order).

### A. `readMany#` — batch-read a fragment's read set
Read (and optimistically validate) all of a fragment's `PRead` TVars in one RTS pass instead of one
`readTVarIO` per node. Delivers the original "validate many at once" goal and, because nothing can
diverge or throw between the batched reads, **shrinks the C-2 zombie window** within the fragment.

### B. Eager write-locking — the dual of `readMany#`
A fragment's write set and targets are fixed in advance, which is the exact precondition for safe
pessimistic locking. At fragment entry: collect the `PWrite` set, **sort by address**, lock it up front
(`lockTVars#`/`stmLockWrites#` via the existing `cond_lock_tvar` CAS); run the body against held locks;
at commit validate the *optimistic* reads, write, bump versions, unpark, unlock. **Hybrid: eager write
locks + optimistic reads** — read concurrency preserved, only writers pessimistic. The address sort is
the canonical order the docs wanted (deadlock/livelock-free, and composes with the fail-fast CAS).

**Correctness obligations:**
- Lock strictly in address order (the static write set gives this for free).
- Reads still validated at commit — locking writes does not protect reads.
- **Abort / `retry` / `throw` must release the held locks** before blocking or unwinding — a fragment
  can sit inside a larger transaction that later retries, so eager locks can outlive the fragment; a
  `retry` while holding them would deadlock the waker. The trec already tracks ownership; the abort
  path must unlock.
- Same-TVar read+write or double-write within a fragment locks once (log already dedups, last write
  wins).

**Tradeoffs — make it adaptive, not the default:**
- **Wins** under high write contention (a locked write set can't be invalidated → far fewer
  aborts/re-runs; the counter-hammered-by-N-threads case).
- **Loses** under low contention (pure overhead vs. optimistic), and for long transactions / large
  write sets: the critical section now spans *[first eager lock … commit]*, which blocks other
  committers longer, makes concurrent **readers** of those TVars see a lock stamp and conflict-retry,
  and risks lock convoys if the holder is descheduled.
- Classic GHC STM is purely optimistic; recommended shape is **opt-in / adaptive** — escalate to eager
  write-locking only after *N* optimistic aborts (contention-detected) or above a write-set-size
  threshold, never unconditionally.

**Combined commit for a fragment:** `lockTVars#` (writes, sorted) → `readMany#` (reads, batched +
validated) → run body → write/unpark/unlock. The two opportunities reinforce each other.

### C. Opting in: an intent combinator, not a mechanism knob

How does a block ask for eager write-locking? A transparent combinator that adds a plan node:

```haskell
SHot :: STMPlan a -> STMPlan a          -- in the AST
hot  :: STM a -> STM a                  -- surface (GHC-only, alongside retry/orElse)
```

On `SHot frag` the interpreter extracts the wrapped fragment's (statically known) write set,
address-sorts, `lockTVars#`, then runs. It is `id` semantically — only contention behavior changes, so
it can **never break a program**; misuse costs only throughput. Its power is bounded by the fragment
requirement: `hot (writeTVar a x *> writeTVar b y)` pre-locks; `hot (do { v <- readTVar a; writeTVar
(pick v) z })` cannot (value-dependent target) and degrades to locking the determinable write prefix.
Composition: idempotent; `hot x <*> hot y` locks the union in one sorted pass; push `hot` inside the
branches of an `orElse`.

**Name it for intent, not mechanism.** Avoid bare `eager` — in Haskell it connotes *evaluation*
strictness, so `eager :: STM a -> STM a` reads like "force this." Prefer **`hot`** (or the sober
`contended`): it names what the programmer *knows* (this block touches a contention point), not the
strategy. That keeps the API stable if the runtime later chooses backoff/HTM/something smarter for
"hot" blocks, and it stays meaningful even on non-fragments where eager-locking can't apply.

**Combinator vs. auto-tuner vs. RTS flags — layer them; don't choose.** They are mechanism / policy /
configuration:

1. **Mechanism (always needed):** `lockTVars#` + fragment write-set extraction. Everything rides on it.
2. **Static hint = the combinator (ship first).** Simplest, correct-by-construction on fragments,
   reproducible, and it captures knowledge the runtime cannot infer — *which* TVar is the hot counter /
   queue tail is usually known at design time, and **library authors can bake `hot` into `TQueue` /
   `TVar`-counter internals** so end users benefit with zero effort.
3. **Auto-tuner = policy on top (later, harder).** Better *when it works* (adapts to unanticipated or
   shifting contention), but **not independent of the static analysis**: to eager-lock on retry it must
   *know* the write set, i.e. assume the previous aborted attempt's set is stable — pure speculation on
   a monadic block, safe only on a fragment. It also needs per-call-site abort state, but STM
   transactions have no stable identity (key off the `atomically` thunk or a per-thread heuristic), and
   its thresholds/hysteresis are opaque and non-reproducible.
4. **RTS flags = the auto-tuner's knobs, not a strategy.** Global eager-locking is the wrong
   granularity (contention is per-TVar) and would tank low-contention workloads; use flags only to set
   the escalation threshold, toggle the tuner, or force-eager for benchmarking.

**The unification (why intent-naming pays off):** have `hot` set the *same* "this node is contended"
bit that the auto-tuner sets when it *detects* contention. One node type (`SHot`), two sources
(explicit annotation + adaptive detection), one mechanism (`lockTVars#`). The programmer seeds the
signal where they know it; the runtime fills in the rest.

---

## Findings

Severity reflects the verifier's revised value. Each finding was independently re-checked against the
code; `[confirmed]`/`[likely]` is the verifier's verdict.

### Critical

#### C-1 — Live `StgTVarWatchQueue` uses a `NULL` terminator the `MUT_PRIM` GC path cannot handle  `[confirmed]`
`rts/STM.c:306,411,856` · `rts/sm/Scav.c:815` · `rts/sm/Evac.c:701` · `rts/sm/NonMovingScav.c:392` · `rts/StgMiscClosures.cmm:763`

`StgTVarWatchQueue` is now a `MUT_PRIM` with **6** pointer fields (was 3). The new per-thread list
links entries via `next_tso_queue_entry`, terminated by `NULL`: the first entry for a trec gets
`next_tso = (StgTVarWatchQueue*)trec->plan == NULL`. The entry is then made GC-reachable (linked into
`tvar->first_watch_queue_entry`, stored in `trec->plan`, TVar dirtied). The moving (`Scav.c:815`),
nonmoving (`NonMovingScav.c:392`), and mark paths iterate `layout.payload.ptrs` and `evacuate`/mark
**every** slot with no `NULL` guard. Result: DEBUG `LOOKS_LIKE_CLOSURE_PTR` assertion; release **major**
GC `get_itbl(NULL)` deref → segfault; nonmoving pushes `NULL` onto the mark queue and derefs it later.
The old 3-field queue used `END_STM_WATCH_QUEUE` and never held `NULL`, which is why the generic path
was safe.

**Fix:** terminate the list with `stg_END_STM_WATCH_QUEUE_closure`; change the `q != NULL` guards
(`register_wait:847`, `validate_and_lock_registered:583`, `unlock_registered_prefix:564`,
`remove_wait_queue_entries_from_list:596`, `trec_wait_list`) to compare against `END`. Strongest
single candidate for "doesn't work yet."

#### C-2 — No incremental read validation: interpreter runs arbitrary Haskell over inconsistent snapshots  `[confirmed]`
`libraries/ghc-internal/src/GHC/Internal/Conc/STM.hs:243-251,290-355,357-378`

`readTVarTx` reads the live `TVar` (`readTVarIO`) at access time and only records `(expected,new)`;
consistency is checked **once**, at commit. Between reads the interpreter runs arbitrary user code
(`SBind` continuations `k a`, case scrutinees, partial matches, `div`/`head`, `unsafeIOToSTM` bodies).
A transaction that has read mutually-inconsistent `TVar`s can (a) loop forever, (b) throw a spurious
`ArithException`/`PatternMatchFail` that escapes `atomically` as `Raise` even though it would never
have committed, or (c) run `unsafeIOToSTM` over garbage. Classic GHC bounds this in the **scheduler**
(`master:rts/Schedule.c:1099` calls `stmValidateNestOfTransactions` on reschedule and aborts zombies —
with a comment giving the exact `[a,b] <- mapM readTVar [ta,tb]; when (a==b) loop` example). Here the
TRec carries no read entries during interpretation, so that check has nothing to validate; the zombie
is never aborted.

**Fix:** add an RTS `validate#` over the log arrays (lock-free, pointer-eq `expected == current`) and
call it before potentially-divergent continuations and at the top-level `Retry`; restart on mismatch.
Cheap interim: re-check existing read-only entries inside `readTVarTx` after each fresh read.

#### C-3 — Global per-TSO `clearRegistrations#` lets `orElse`/`catchSTM` siblings clobber each other's wait sets  `[confirmed]`
`libraries/ghc-internal/src/GHC/Internal/Conc/STM.hs:273-288,314-336` · `rts/STM.c:842-873,945-959`

`register_wait` appends to the single per-TSO list (`trec->plan`); `stmClearRegistrations` removes
**all** of it. The interpreter calls `clearRegistrationsIO` mid-interpretation — in `runRightAlternative`
on Ok/Raise (`:278,281`) and in `SCatch`'s Raise branch (`:335`). The top-level `RetryWithWait` arm
(`:373`) then blocks **without** re-registering, trusting whatever survived.

**Concrete lost wakeup:** `orElse a (catchSTM bRaises hRetry)` where `a` reads `A` and retries, `b`
raises, handler `h` reads `B` and retries. Trace: left retries → registers wait on `A` (`:322`) →
`SCatch` body raises → `clearRegistrationsIO` **wipes A** (`:335`) → handler reads `B`, retries →
`runRightAlternative` registers only `B` → `SOrElse` yields `RetryWithWait` → top loop blocks on **B
only**. A change to `A` never wakes the thread.

*Verifier correction:* the Ok/commit clears are actually correct (that path never blocks); the
load-bearing defect is specifically a clear that fires while sibling registrations are live **and** the
transaction still ends up blocking — the `SCatch`-Raise path is the clearest trigger.

**Fix:** stop registering mid-interpretation; register the final union once in `runAtomically` on
`Retry` (the RTS already dedups per-TVar). Eliminates `RetryWithWait` and the clobber together.

#### C-4 — `registerLogRange#` has no JS codegen handler (non-exhaustive `genPrim`)  `[confirmed]`
`compiler/GHC/StgToJS/Prim.hs:922-934` · `compiler/GHC/Builtin/primops.txt.pp:3176`

`genPrim` is a total, wildcard-free `case`. `registerLogRange#` is live (used on every retry path:
`STM.hs:199` ← `registerRetriesLog`) but has no branch. Under `-Werror` (used for these modules) this
is a compile failure of `Prim.hs` itself; otherwise a codegen pattern-match panic. The C/Cmm/JS bodies
are all wired (`PrimOps.cmm:1209`, `STM.c:894`, `js/stm.js:97 h$registerLogRange`) — only the genPrim
dispatch is missing.

**Fix:** add a `RegisterLogRangeOp` case calling `h$registerLogRange` (+ `hdRegisterLogRangeStr`).

#### C-5 — `stmCommitLog#` JS handler binds a nonexistent `flags` argument  `[confirmed]`
`compiler/GHC/StgToJS/Prim.hs:925-926` · `rts/PrimOps.cmm:1181` · `rts/js/stm.js:70`

`stmCommitLog#` takes 4 value args `(tvars, expected, newvals, len)` (`primops.txt.pp:3155`); `State#`
is zero-width in JS so `genArg` yields exactly 4 expressions. The handler destructures a 5-element
pattern `[tvars, expected, newvals, flags, len]` → irrefutable pattern failure → GHC panic compiling
any STM-using module on JS. Every other layer agrees on 4 args; `flags` exists nowhere.

**Fix:** bind `[tvars, expected, newvals, len]`.

### High

#### H-1 — `free_stg_tvar_watch_queue` zeroes traced pointer fields without nonmoving deletion barriers (use-after-free of `expected`)  `[confirmed]`
`rts/STM.c:355-367,593` · `rts/sm/NonMovingMark.c:434`

Now zeroes `next_tso_queue_entry`/`tvar`/`expected`/`closure`, but the `IF_NONMOVING` barrier only
pushes the old `next_queue_entry` + freelist head — not the old `tvar`/`expected`/`closure`. The freed
entry stays reachable via `trec->plan` until `:616`. Under concurrent nonmoving mark, the `expected`
snapshot (possibly the sole reference, after the registering array is collected) can be reclaimed while
the blocked transaction still needs it (`validate_and_lock_registered` reads `q->expected`, `:584`) →
use-after-free. Master leaves these fields intact precisely to avoid this.

**Fix (a, preferred):** stop zeroing on free — `stmPreGCHook` drops the freelist wholesale, so zeroing
buys no GC-safety. **(b):** push old values under `IF_NONMOVING_WRITE_BARRIER_ENABLED`.

#### H-2 — `register_wait` overwrites `q->expected` in place with no write barrier  `[confirmed]`
`rts/STM.c:847-852`

The re-registration branch (same TVar already in the list) does `q->expected = expected;` with no
barrier — overwriting a traced `MUT_PRIM` field that may already be in the nonmoving snapshot. Every
other overwrite in the file barriers the old value; the fresh-entry path right below (`:867-869`) does
too. Master's `stmWriteTVar` establishes the exact precedent. Reachable via overlapping `orElse`
read sets (verifier-confirmed `register_wait` is live through `stmRegisterLogRange`).

**Fix:** `IF_NONMOVING_WRITE_BARRIER_ENABLED { updateRemembSetPushClosure(cap, q->expected); }` before
the store.

#### H-3 — Immutable-list `TxLog` is O(n²) in distinct TVars  `[confirmed · practical urgency: low]`
`libraries/ghc-internal/src/GHC/Internal/Conc/STM.hs:106,124-135,243-261`

`type TxLog = [TxEntry]`. `readTVarTx`/`writeTVarTx` do `lookupTxLog` (O(n) scan) then, on miss/update,
`insertTxLog` which rebuilds the **entire spine** to append at the tail (O(n) time + O(n) fresh cons
cells). n distinct TVars ⇒ ΣO(i) = **O(n²)** time and allocation. *Verifier: the cost is even higher —
two full traversals per miss.* `stm_large_log.hs` (n=64/65) walks exactly this path. Directly
contradicts the documented SoA log (`STM-free-applicative.md:206-241`).

**Downgraded.** Real but bounded — it only bites pathologically large single transactions (thousands of
TVars), not STM's intended sizes (`stm_large_log`'s 64 reads are ~4k cons scans, negligible). **Do not
fix this with mutable arrays** — that reintroduces the GC-barrier fragility behind C-1/H-1/H-2/M-1.
**Fix:** keep the list; switch insert to cons-front + first-match `lookup` (O(1) insert, no spine
rebuild — a constant-factor + GC-churn win, not an asymptotic one; linear lookup is irreducible here).
Accept and document the O(n²); if huge transactions ever matter, add a *rebuildable* address index
dropped on rollback, never in-place mutation. See "The elegant target."

#### H-4 — Per-commit/per-retry fresh `SmallArray` allocation + full copy, no reuse across attempts  `[confirmed · practical urgency: low]`
`libraries/ghc-internal/src/GHC/Internal/Conc/STM.hs:212-241,357-378`

`commitTxLog` does `length log` (O(n)), allocates **three** arrays, walks the list again copying;
`registerRetriesLog` does the same with two. `runAtomically` restarts with `go emptyTxLog` on every
conflict/retry, so nothing is reused and the whole plan + list are rebuilt each attempt. The design
mandates `resetTxLog` (len=0, reuse arrays) and handing the arrays directly to the primops with no copy.

**Downgraded** (same bounded scope as H-3). Marshalling to arrays at the primop boundary is unavoidable
(Cmm can't walk a Haskell list), but it is O(distinct) and runs once per attempt. **Fix:** cons-front
insert removes the per-write spine reallocation; track `len` incrementally to drop the separate
`length` pass; dedup during the single marshalling walk. Keep immutability (so rollback stays free)
rather than reusing mutable arrays across attempts.

#### H-5 — Design docs vs code disagree on the core log model; docs are stale and self-labeled "authoritative"  `[confirmed]`
`rts/STM-plan.md:206-253` · `rts/STM-free-applicative.md:42-50` · `libraries/ghc-internal/.../Conc/STM.hs:102-150`

The docs (`STM-plan.md` §3/§4 — self-described as "the authoritative, step-by-step plan") specify a
mutable SoA log with `pushScope`/`rollbackScope`/shadow entries/`findIndex`/`cap`/`len`. **None of it
exists.** The code is `[TxEntry]` with persistent-list rollback (re-evaluate the right branch/handler
against the captured prior `log`). An engineer debugging against the docs will mis-reason about
rollback entirely.

**Fix:** converge docs→code — the immutable list is what ships and what *should* ship (SoA is rejected
as fragile; see "The elegant target"). Delete the `pushScope`/`rollbackScope`/shadow-entry/SoA prose
entirely and document the two-list (`log` + monotone `waitSet`) model instead.

#### H-6 — Undocumented 4th outcome `RetryWithWait` contradicts the docs' 3-outcome model and hides the orElse wait-union invariant  `[confirmed]`
`libraries/ghc-internal/src/GHC/Internal/Conc/STM.hs:108,273-289,314-325,357-378` · `rts/STM-free-applicative.md:36-40,255-281,315-323`

The docs define `Ok | Retry | Raise`. The code adds `RetryWithWait`, meaning "a retry whose waits were
already installed by a nested branch, so the top loop must block but not re-register." This is the
subtlest invariant in the executor and lives **only** in an undocumented constructor whose name doesn't
convey it. Anyone editing retry/orElse can double-register or fail to register → lost/spurious wakeups.

**Fix:** eliminate it. With the two-list model (`log` + monotone reads-only `waitSet`), `orElse` returns
plain `Retry`, the `waitSet` already carries the union, and `runAtomically` registers once at the top —
so there is no "already registered?" state to track. See "The elegant target."

#### H-7 — `interface-stability` `ghc-prim-exports.stdout` is stale vs. the actual primops  `[confirmed]`
`testsuite/tests/interface-stability/ghc-prim-exports.stdout:2611` · `compiler/GHC/Builtin/primops.txt.pp:3155,3176`

`stmCommitLog#` in the baseline carries a phantom `MutableByteArray#` arg (dropped in commit
`2aa5025f09`), and `registerLogRange#` is absent entirely (grep count 0). The baseline's last-touching
commit predates the primop change. The test diffs `dump-decls` against these snapshots → guaranteed
failure, and it masks any real ABI drift. *Verifier dropped several secondary claims in the original
finding (no "+/-" diff format; `catchRetry#`/`readTVar#` are not referenced); the core mismatch holds,
incl. the `-mingw32` variant.*

**Fix:** freeze the primop set, then regenerate the baselines.

#### H-8 — `stm_orElse_wait_union` does not actually test the wait-set **union**  `[confirmed]`
`testsuite/tests/stm/stm_orElse_wait_union.hs:11`

It reads `a` (left) and `b` (right), both retry, then writes **only `b`** and asserts wake. It never
writes `a`, so it cannot detect a missing registration of the left branch's reads (or of TVars read
*before* the orElse) — exactly the C-3 failure mode. The most important orElse property is effectively
untested; an incomplete union would keep the suite green.

**Fix:** add cases that wake when **only the left-branch TVar** is written, and when **only a TVar read
before the orElse** is written. Both must wake under a timeout.

### Medium

- **M-1 — `sort_log_arrays` permutes array pointer slots with no nonmoving barrier** `[confirmed]`
  `rts/STM.c:415-438,766-769`. In-place permutation without `updateRemembSetPushClosure`;
  `recordClosureMutated` runs after and only satisfies generational rescan, not the SATB snapshot.
  Usually masked (arrays freshly allocated pre-snapshot, values also reachable elsewhere) but not
  provably safe. **Fix:** push old slots under `IF_NONMOVING`, or sort in the Haskell layer so the RTS
  never mutates the arrays.
- **M-2 — Sanity checker rejects `NULL` watch-queue fields and has no STM-specific coverage** `[confirmed]`
  `rts/sm/Sanity.c:410` · `rts/TraverseHeap.c:507`. `TREC_CHUNK`'s explicit case was deleted; the new
  layouts flow through generic `MUT_PRIM` which asserts non-`NULL`. Surfaces C-1 and leaves
  STM-specific invariants (back-link consistency, `trec->plan` ↔ `first_watch_queue_entry`) unchecked.
  **Fix:** fix C-1 first, then add an explicit `checkClosure` case.
- **M-3 — Single `writeTVar` falls to the slow interpreter path** `[confirmed]`
  `libraries/ghc-internal/.../Conc/STM.hs:472-494`. `fastPrim` handles `PRead`/`PNewTVar` but not
  `PWrite`, so `atomically (writeTVar tv x)` (counters, flags, TMVar puts — the most common trivial op)
  builds a log, allocates three arrays, sorts, locks, commits. **Fix:** add a `PWrite` fast path
  (direct one-TVar locked commit, no array/sort).
- **M-4 — `TArray.newArray` uses `unsafeIOToSTM`, leaving the applicative fragment** `[confirmed]`
  `libraries/stm/Control/Concurrent/STM/TArray.hs:88`. `unsafeIOToSTM` → `SUnsafeIO`, which isn't
  `SPure`/`SPrim`/`SApp`, so `planApply` (`STM.hs:100`) falls to the `SBind` case — any `<*>` involving
  a `TArray` collapses the whole transaction out of the `SApp` fragment. Contradicts the design goal and
  the earlier "keep TArray in applicative fragment" commit. **Fix:** reintroduce an in-fragment
  allocation node (`PNewTVar` batch, or `traverse (const (newTVar e))`).
- **M-5 — `base-exports` baseline still describes the old `STM` newtype** `[confirmed]`
  `testsuite/tests/interface-stability/base-exports.stdout:5057`. Records
  `newtype STM a = STM (State# … -> …)`; the new rep is `STM { stmPlan :: STMPlan a }`. Test fails until
  regenerated; confirm the `STM` constructor no longer leaks (it must not — `STMPlan` is internal).
- **M-6 — `STMApp`/`STMAppTail` free-applicative type from the docs does not exist** `[confirmed]`
  `rts/STM-plan.md:142-205` vs `Conc/STM.hs:61-100`. Code uses flat `SPrim`/`SApp` + `planMap`/`planApply`
  (and spells it `SApp`, not `SAp`). **Fix:** rewrite docs §1/§2 to the actual constructors.
- **M-7 — `registerWait#` primop + JS `h$stmWait`/`h$stmResumeRetry_e` are dead code** `[confirmed]`
  `primops.txt.pp:3166-3174` · `rts/js/stm.js:131-172`. No Haskell caller for `registerWait#`; the JS
  retry path is now `h$blockOnRegistered`/`h$registerLogRange`. (`register_wait` the C helper stays —
  used internally by `stmRegisterLogRange`.) **Fix:** remove the `registerWait#` primop surface and the
  dead JS closures.
- **M-8 — Removing `UnliftedTVar1/2` drops the only coverage of unlifted TVar contents; `.stdout` orphaned** `[confirmed]`
  `testsuite/tests/primops/should_run/all.T`. The transactional primops they exercised were deleted;
  the new path coerces every value through `Any`. `.hs` removed in `a6302482ba` but `UnliftedTVar1.stdout`
  (and `T23142.stdout`) left orphaned — an incomplete deletion, not a considered coverage decision.
  **Fix:** keep a minimal unlifted-content test through the supported surface, or delete the orphans and
  document the dropped capability.
- **M-9 — `stm_orElse_rollback` too weak; commit-conflict re-run and async-exception paths untested** `[confirmed]`
  `testsuite/tests/stm/stm_orElse_rollback.hs:8`. Only checks the value *within* the transaction, never
  reads the TVar after `atomically` to confirm the discarded write didn't leak. `stm_stress` can't
  distinguish a correct conflict re-run from balanced lost updates. Async exception during a transaction
  has zero coverage. **Fix:** read-after, deterministic exactly-once conflict test, `throwTo`-mid-txn test.
- **M-10 — `mfix`/`SFix` divergence path and nested-orElse registration accumulation have no targeted tests** `[confirmed]`
  `Conc/STM.hs:343,273`. No test drives a recursive `mfixSTM`, a retrying/throwing `mfixSTM`, or a
  2+-deep nested `orElse` asserting a wake on *any* branch's read set. **Fix:** add them.

### Low

- **L-1 — `config_use_read_phase` read validation hinges on an undocumented invariant** `[confirmed]`
  `rts/STM.c:485-552`. Sound as written (double-load + `num_updates`), but correctness depends on *every*
  committer that changes `current_value` also bumping `num_updates` (enforced by the `expected==new`
  suppression). **Fix:** add an assertion/comment at `commit_log_entries` documenting the invariant.
- **L-2 — Per-attempt insertion sort by TVar address in the commit hot path** `[likely]`
  `rts/STM.c:415-438,765-766`. O(n²) worst case, stacked on the O(n²) log build, inside the critical
  section; required every attempt because no stable `tvar_id` exists. **Fix:** keep insertion sort for
  tiny logs, switch to O(n log n) (sort an index permutation) for larger.
- **L-3 — `orElse` retry path does O(n·m) `differenceTxLog` + double registration** `[confirmed]`
  `Conc/STM.hs:139-150,314-324`. **Fix:** the two-list model deletes this — `orElse` extends the monotone
  `waitSet` and registers once at the top, so `differenceTxLog`/`tvarInLog` and per-branch registration
  disappear entirely (no scope-delta diffing). See "The elegant target."
- **L-4 — `lookupTxLog`/`insertTxLog` lean on `unsafeCoerce#` + `eqAddr#` on coerced `TVar#`** `[confirmed]`
  `Conc/STM.hs:119-135`. Sound (address-keyed, value type erased) but a logic bug storing a value at the
  wrong type is silently mis-coerced rather than caught. **Fix:** document the per-transaction
  fixed-type invariant; minimize coercion sites.
- **L-5 — Dead JS code: `h$stmWait`, `h$stmResumeRetry_e`, `hdReadTVar`/`hdWriteTVar`** `[likely]`
  `rts/js/stm.js:131-172` · `StgToJS/Rts/Rts.hs:643-652` · `StgToJS/Symbols.hs:712-719`. **Fix:** delete.
- **L-6 — Dead placeholders: `emptyAny`, the bespoke `STMResult` record** `[confirmed]`
  `Conc/STM.hs:110-114,343-355`. `emptyAny` is a never-read array init (smell); `STMResult` is a one-off
  3-field record used only inside `SFix`. **Fix:** make `emptyAny` a genuinely-bottom `raise#` so a stray
  read faults; reuse the standard `(STMOutcome a, TxLog)` shape in `SFix`.
- **L-7 — `trec->plan` field overloaded as "wait-queue head," a leftover name from the deleted `StgSTMPlan`** `[confirmed]`
  `rts/STM.c:103,411-413,873`. Docs say the RTS no longer uses plans, yet the field is named `plan`.
  **Fix:** rename to `wait_queue`/`registrations`.
- **L-8 — `mfix`/`SFix` uses `errorWithoutStackTrace` where docs promise black-hole/divergence** `[likely]`
  `Conc/STM.hs:343-355` vs `STM-free-applicative.md:68-74`. Raising a catchable error is observably
  different from the legacy black hole. *Verifier (uncertain): the headline divergence framing is
  inaccurate — under a strict self-dependent knot GHC's blackholing fires first and the error branch is
  unreachable; but the deeper concern is real — the `let ans = … m s0 …; r = … ans …` lazy-State# knot is
  exactly the pattern `fixST`/`fixIO` abandoned (Note [fixST], #15349) because lazy blackholing can
  **re-run** the effectful body, duplicating reads/registrations.* **Fix:** decide the semantics; if
  matching legacy, use explicit blackholing like `fixIO`/`fixST` rather than the lazy knot, and align docs.

### Confirmed-correct (positives worth keeping)

- **RTS commit path is internally sound** — `sort_log_arrays` permutes all three arrays together;
  `expected==new` correctly suppresses locks/version-bumps/wakeups; `num_updates` indexed consistently;
  `TREC_HEADER` (2 ptrs) / `TVAR_WATCH_QUEUE` (6 ptrs) layouts match `Closures.h`.
- **Capability STM freelists are correctly GC-dropped** via `stmPreGCHook` (not roots); the
  `cond_lock_tvar` remembered-set fix from `STM.md` is correctly applied.
- **`tryPeekTQueue`/`TBQueue` rework** (read+unGet → `fmap Just (peek…) \`orElse\` return Nothing`) is a
  correct, strictly-better simplification.
- **`MonadFix STM` relocation** from the stm library into ghc-internal is correctly wired across the repo
  boundary (CPP-gated for `base>=4.22`).
- **`PWrite` exclusion from the read fast path is correct** (a lone write must still commit).

---

## Contested / refuted (so they don't get re-raised)

The adversarial pass **refuted** several plausible-sounding claims. Notably:

- **"`blockOnRegistered` deadlocks against the address-sorted committer (AB-BA lock order)."** **Refuted.**
  Both paths acquire locks via `cond_lock_tvar` — a **single non-blocking CAS** that fails fast and
  releases on contention (`rts/STM.c:218-234,480,583-588`). No path blocks while holding a lock, so no
  cyclic deadlock forms; worst case is transient livelock/retry. *Caveat: the cross-layer synthesis still
  listed lock-order as a concern and flagged it as needing a threaded-RTS stress test to rule out a
  livelock pathology — treat "deadlock" as refuted, "livelock under heavy contention" as unverified, not
  proven absent.* The `validate#`/single-sorted-registration direction (root cause 1/3) makes the whole
  question moot.
- **"`RetryWithWait` makes the retry/commit contract incoherent / drops left-branch waits on normal
  nesting."** **Refuted.** Registrations *accumulate* in the per-TSO trec list and dedup per-TVar;
  `runRightAlternative` always registers the full `logR` (⊇ entering log), so normal nested `orElse`
  preserves the union. (The *real* defect is narrower — the mid-flight **clear** in C-3, not the
  accumulation.) `RetryWithWait` is still worth removing for clarity (H-6).
- **"`newTVar` inside a transaction isn't rolled back on Retry/Raise."** **Refuted** — matches legacy STM
  semantics (allocation is not transactional; the new TVar is simply unreachable after abort).
- **"Unbarriered relink of `pq->next_queue_entry` when removing a non-head entry."** **Refuted** — the
  removed node is on the freelist path covered by `stmPreGCHook`.
- **"`h$blockOnRegistered` calls undefined `h$rs()`" / "`h$TVarsWaiting` not GC-traced."** **Refuted** —
  `h$rs` is a long-standing helper (`thread.js:1486`); the wait map is reachable via the thread/TVar
  graph.
- **"`SApp`/`SBind` short-circuit diverges from applicative-evaluates-whole-fragment semantics."**
  **Refuted** — based on a misreading of `evalSTM`'s `SApp` case.
- **"No coverage of catchSTM rollback."** **Refuted** — covered by in-scope submodule tests
  (`libraries/stm/tests/stm061.hs`, `T2411.hs`); catchSTM rollback semantics are unchanged by the rewrite.
  (The `expected==new` no-wakeup sub-gap is real — folded into M-9/M-10.)
- **"Docs claim log retained across retries but code resets."** **Uncertain/mostly refuted** — the doc
  retention requirement is "across `blockOnRegistered#`" (within one attempt), which the code satisfies;
  the genuine issue is the broader SoA-vs-list divergence already captured in H-5.

---

## Cross-layer issues (missed by per-dimension finders)

1. **Incremental validation and the orElse wait-union are the same missing primitive.** One `validate#`
   over the log arrays (lock-free, address-sorted, pointer-eq) closes the zombie critical (C-2) **and**
   gives a correct wait-union (C-3) — call it before divergent continuations and at the top-level Retry.
2. **`free_stg_tvar_watch_queue` zeroing (GC) × `validate_and_lock_registered` reading `q->expected`
   (RTS).** The wake/revalidate path reads exactly the field the free path nulls without a barrier — a
   precise nonmoving use-after-free on the revalidation path. Stop zeroing on free (H-1) closes it.
3. **Registration tangle = log overload, not log type.** The single `[TxEntry]` list serving both the
   rollback view and the wait-set union is the common root of C-3, H-6, and L-3. Splitting into `log` +
   monotone `waitSet` (not switching to arrays) fixes all three at once, and is independent of the
   bounded O(n²) perf issue (H-3/H-4).
4. **Dead-code incoherence:** the JS handler list simultaneously lacks a live op (`registerLogRange#`) and
   carries dead ops (`registerWait#`, `h$stmWait`) — the backend was never re-derived against the final
   primop set after the `registerLogRange` redesign.

---

## Prioritized fix plan

1. **GC safety (unblocks everything — nothing survives GC today):** replace the `NULL` terminator with
   `stg_END_STM_WATCH_QUEUE_closure`; switch all `q != NULL` guards to `END`. Add a `checkClosure` case
   for the watch queue. *(C-1, M-2)*
2. **GC use-after-free:** stop zeroing pointer fields in `free_stg_tvar_watch_queue`; barrier the old
   value before `q->expected = …` in `register_wait`; barrier `sort_log_arrays` (or sort in Haskell).
   *(H-1, H-2, M-1)*
3. **JS codegen:** bind 4 args for `StmCommitLogOp`; add the `RegisterLogRangeOp` case; delete dead JS
   retry code and the `registerWait#` surface. *(C-4, C-5, M-7, L-5)*
4. **Incremental validation (core correctness):** add `validate#` and call it before divergent
   continuations and at the top-level Retry; restart on mismatch. *(C-2)*
5. **Log shape (keep it immutable):** split the list into `log` (rolled back by `orElse`/`catchSTM`) +
   monotone reads-only `waitSet`; switch insert to cons-front + first-match lookup; dedup at the
   marshalling boundary. Do **not** adopt mutable SoA arrays. *(H-3, H-4, L-3)*
6. **Registration model:** eliminate `RetryWithWait` and all mid-flight registration; the monotone
   `waitSet` carries the union and `runAtomically` registers once on `Retry`; one address-sorted lock
   order for commit and wait. *(C-3, H-6)*
7. **Perf fast path:** add a `PWrite` single-TVar fast path; O(n log n) sort for large logs. *(M-3, L-2)*
8. **Submodule:** replace `TArray.newArray`'s `unsafeIOToSTM` with an in-fragment node. *(M-4)*
9. **Tests + docs:** regenerate `interface-stability` baselines after freezing the primop set; delete
   orphaned `.stdout`; add real orElse-union, mfix, async-exception-mid-txn, and exactly-once
   conflict-re-run tests; rewrite the design docs to the converged model and settle the mfix divergence
   semantics. *(H-5, H-7, H-8, M-5..M-10, L-6..L-8)*

---

## Open questions / needs runtime verification (couldn't confirm read-only)

1. Whether heavy `orElse` contention produces a *livelock* (deadlock is refuted) — needs a threaded-RTS
   stress run.
2. The nonmoving use-after-free findings (H-1, H-2, M-1) are GC-timing-dependent and were **not
   reproduced** — confirm with `+RTS --nonmoving-gc` + DEBUG sanity stress.
3. `SFix` happy-path knot-tying (a recursive value across TVars) is untested and unverified; only the
   error-vs-diverge semantics were analyzed.
4. The `unsafeIOToSTM` × missing-validation interaction (IO over inconsistent state) is doubly dangerous
   and needs its own test/decision.
5. The O(n²) perf claims are static; quantify against `master` with `stm_large_log`.

---

*Generated by a read-only multi-agent review (60 agents): 8 subsystem finders → adversarial
verification of each finding → cross-layer synthesis. Severities are post-verification. Line numbers
are accurate as of the reviewed working tree; re-confirm before editing.*
