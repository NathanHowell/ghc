/* -----------------------------------------------------------------------------
 * (c) The GHC Team 1998-2005
 *
 * STM implementation.
 *
 * Overview
 * --------
 *
 * See the PPoPP 2005 paper "Composable memory transactions".  In the current
 * implementation, each transaction has a TRec header tracking its state and
 * any wait bundle. TVar accesses are recorded by the Haskell STM interpreter
 * into log arrays (tvars/expected/new) and passed to the RTS for
 * sorting, validation, and commit. Waiting uses per-TVar registrations.
 *
 * The RTS only tracks top-level transaction state; retry/orElse/catch handling
 * lives in the Haskell plan interpreter.
 *
 * Concurrency control
 * -------------------
 *
 * Three different concurrency control schemes can be built according to the
 * settings in STM.h:
 *
 * STM_UNIPROC assumes that the caller serialises invocations on the STM
 * interface.  In the Haskell RTS this means it is suitable only for
 * non-THREADED_RTS builds.
 *
 * STM_CG_LOCK was a historic locking mode using coarse-grained locking
 * It has been removed, look at the git history if you are interest in it.
 *
 * STM_FG_LOCKS uses fine-grained locking -- locking is done on a per-TVar basis
 * and, when committing a transaction, no locks are acquired for TVars that have
 * been read but not updated.
 *
 * Concurrency control is implemented in the functions:
 *
 *    lock_tvar / cond_lock_tvar
 *    unlock_tvar
 *
 * The choice between STM_UNIPROC / STM_FG_LOCKS affects the
 * implementation of these functions.
 *
 * lock_tvar / cond_lock_tvar and unlock_tvar are more complex because they have
 * other effects (present in STM_UNIPROC builds) as well as the
 * actual business of manipulating a lock (present only in STM_FG_LOCKS builds).
 * This is because locking a TVar is implemented by writing the lock holder's
 * TRec into the TVar's current_value field:
 *
 *   lock_tvar - lock a specified TVar (STM_FG_LOCKS only), returning the value
 *               it contained.
 *
 *   cond_lock_tvar - lock a specified TVar (STM_FG_LOCKS only) if it
 *               contains a specified value.  Return true if this succeeds,
 *               false otherwise.
 *
 *   unlock_tvar - release the lock on a specified TVar (STM_FG_LOCKS only),
 *               storing a specified value in place of the lock entry.
 *
 * Using these operations, the typical pattern of a commit/validate/wait
 * operation is to (a) lock the STM, (b) lock all the TVars being updated, (c)
 * check that the TVars that were only read from still contain their expected
 * values, (d) release the locks on the TVars, writing updates to them in the
 * case of a commit, (e) unlock the STM.
 *
 * Queues of waiting threads hang off the first_watch_queue_entry field of each
 * TVar.  This may only be manipulated when holding that TVar's lock.  In
 * particular, when a thread is putting itself to sleep, it mustn't release the
 * TVar's lock until it has added itself to the wait queue and marked its TSO as
 * BlockedOnSTM -- this makes sure that other threads will know to wake it.
 *
 * ---------------------------------------------------------------------------*/

#include "rts/PosixSource.h"
#include "Rts.h"
#include "RtsFlags.h"

#include "RtsUtils.h"
#include "Schedule.h"
#include "STM.h"
#include "Trace.h"
#include "Threads.h"
#include "sm/Storage.h"
#include "SMPClosureOps.h"
#include "AllocArray.h"

#include <stdio.h>

/*......................................................................*/

#define TRACE(_x...) debugTrace(DEBUG_stm, "STM: " _x)

// Log-based execution uses trec->wait_queue to carry per-thread registrations.
// It is the head of a singly-linked StgTVarWatchQueue list threaded through the
// next_tso_queue_entry field and terminated by stg_END_STM_WATCH_QUEUE_closure
// (never NULL): the watch-queue closures are MUT_PRIM, and the generic GC
// scavenger/marker walks every pointer slot unconditionally, so a NULL slot in a
// live entry would be dereferenced as a closure. Every traversal below therefore
// compares against END_STM_WATCH_QUEUE rather than NULL.

// Stack buffer size for per-log num_updates snapshots.
#define STM_NUM_UPDATES_STACK_LIMIT 64

// If SHAKE is defined then validation will sometimes spuriously fail.  They help test
// unusual code paths if genuine contention is rare
#if defined(SHAKE)
static int shake_ctr = 0;
static int shake_lim = 1;

static int shake(void) {
    if (((shake_ctr++) % shake_lim) == 0) {
      shake_ctr = 1;
      shake_lim ++;
      return true;
    }
    return false;
}
#else
static int shake(void) {
    return false;
}
#endif

/*......................................................................*/

// if REUSE_MEMORY is defined then attempt to re-use descriptors and wait queue
// entries without GC

#define REUSE_MEMORY

/*......................................................................*/

#if defined(STM_UNIPROC)
static const StgBool config_use_read_phase = false;

static StgClosure *lock_tvar(Capability *cap STG_UNUSED,
                             StgTRecHeader *trec STG_UNUSED,
                             StgTVar *s STG_UNUSED) {
  StgClosure *result;
  TRACE("%p : lock_tvar(%p)", trec, s);
  result = ACQUIRE_LOAD(&s->current_value);
  return result;
}

static void unlock_tvar(Capability *cap,
                        StgTRecHeader *trec STG_UNUSED,
                        StgTVar *s,
                        StgClosure *c,
                        StgBool force_update) {
  TRACE("%p : unlock_tvar(%p)", trec, s);
  if (force_update) {
    StgClosure *old_value = ACQUIRE_LOAD(&s->current_value);
    RELEASE_STORE(&s->current_value, c);
    dirty_TVAR(cap, s, old_value);
  }
}

static StgBool cond_lock_tvar(Capability *cap STG_UNUSED,
                              StgTRecHeader *trec STG_UNUSED,
                              StgTVar *s STG_UNUSED,
                              StgClosure *expected) {
  StgClosure *result;
  // TRACE("%p : cond_lock_tvar(%p, %p)", trec, s, expected);
  result = ACQUIRE_LOAD(&s->current_value);
  // TRACE("%p : %s", trec, (result == expected) ? "success" : "failure");
  return (result == expected);
}
#endif

#if defined(STM_FG_LOCKS) /*...................................*/

static const StgBool config_use_read_phase = true;

static StgClosure *lock_tvar(Capability *cap,
                             StgTRecHeader *trec,
                             StgTVar *s STG_UNUSED) {
  StgClosure *result;
  // TRACE("%p : lock_tvar(%p)", trec, s);
  do {
    const StgInfoTable *info;
    do {
      result = ACQUIRE_LOAD(&s->current_value);
      info = GET_INFO(UNTAG_CLOSURE(result));
    } while (info == &stg_TREC_HEADER_info);
  } while (cas((void *) &s->current_value,
               (StgWord)result, (StgWord)trec) != (StgWord)result);


  IF_NONMOVING_WRITE_BARRIER_ENABLED {
      if (result)
          updateRemembSetPushClosure(cap, result);
  }
  return result;
}

static void unlock_tvar(Capability *cap,
                        StgTRecHeader *trec STG_UNUSED,
                        StgTVar *s,
                        StgClosure *c,
                        StgBool force_update STG_UNUSED) {
  // TRACE("%p : unlock_tvar(%p, %p)", trec, s, c);
  ASSERT(ACQUIRE_LOAD(&s->current_value) == (StgClosure *)trec);
  RELEASE_STORE(&s->current_value, c);
  dirty_TVAR(cap, s, (StgClosure *) trec);
}

static StgBool cond_lock_tvar(Capability *cap,
                              StgTRecHeader *trec,
                              StgTVar *s,
                              StgClosure *expected) {
  StgClosure *result;
  StgWord w;
  // TRACE("%p : cond_lock_tvar(%p, %p)", trec, s, expected);
  w = cas((void *)&(s -> current_value), (StgWord)expected, (StgWord)trec);
  result = (StgClosure *)w;
  IF_NONMOVING_WRITE_BARRIER_ENABLED {
      if (result == expected) {
          updateRemembSetPushClosure(cap, expected);
      }
  }
  // TRACE("%p : %s", trec, result ? "success" : "failure");
  return (result == expected);
}
#endif

/*......................................................................*/

// Helper functions for thread blocking and unblocking

static void park_tso(StgTSO *tso) {
  ASSERT(tso -> why_blocked == NotBlocked);
  tso -> block_info.closure = (StgClosure *) END_TSO_QUEUE;
  RELEASE_STORE(&tso -> why_blocked, BlockedOnSTM);
  TRACE("park_tso on tso=%p", tso);
}

static void unpark_tso(Capability *cap, StgTSO *tso) {
    // We will continue unparking threads while they remain on one of the wait
    // queues: it's up to the thread itself to remove it from the wait queues
    // if it decides to do so when it is scheduled.

    // Only the capability that owns this TSO may unblock it. We can
    // call tryWakeupThread() which will either unblock it directly if
    // it belongs to this cap, or send a message to the owning cap
    // otherwise.

    // TODO: This sends multiple messages if we write to the same TVar multiple
    // times and the owning cap hasn't yet woken up the thread and removed it
    // from the TVar's watch list. We tried to optimise this in D4961, but that
    // patch was incorrect and broke other things, see #15544 comment:17. See
    // #15626 for the tracking ticket.

    // Safety Note: we hold the TVar lock at this point, so we know
    // that this thread is definitely still blocked, since the first
    // thing a thread will do when it runs is remove itself from the
    // TVar watch queues, and to do that it would need to lock the
    // TVar.

    tryWakeupThread(cap,tso);
}

static void unpark_waiters_on(Capability *cap, StgTVar *s) {
  StgTVarWatchQueue *q;
  StgTVarWatchQueue *trail;
  TRACE("unpark_waiters_on tvar=%p", s);
  // unblock TSOs in reverse order, to be a bit fairer (#2319)
  for (q = ACQUIRE_LOAD(&s->first_watch_queue_entry), trail = q;
       q != END_STM_WATCH_QUEUE;
       q = q -> next_queue_entry) {
    trail = q;
  }
  q = trail;
  for (;
       q != END_STM_WATCH_QUEUE;
       q = q -> prev_queue_entry) {
      unpark_tso(cap, (StgTSO *)(q -> closure));
  }
}

/*......................................................................*/

// Helper functions for downstream allocation and initialization

static StgTVarWatchQueue *new_stg_tvar_watch_queue(Capability *cap,
                                                   StgTSO *tso,
                                                   StgTVar *tvar,
                                                   StgClosure *expected,
                                                   StgTVarWatchQueue *next_tso) {
  StgTVarWatchQueue *result;
  result = (StgTVarWatchQueue *)allocate(cap, sizeofW(StgTVarWatchQueue));
  SET_HDR (result, &stg_TVAR_WATCH_QUEUE_info, CCS_SYSTEM);
  result -> closure = (StgClosure *)tso;
  result -> tvar = tvar;
  result -> expected = expected;
  result -> next_tso_queue_entry = next_tso;
  result -> next_queue_entry = END_STM_WATCH_QUEUE;
  result -> prev_queue_entry = END_STM_WATCH_QUEUE;
  return result;
}

static StgTRecHeader *new_stg_trec_header(Capability *cap) {
  StgTRecHeader *result;
  result = (StgTRecHeader *) allocate(cap, sizeofW(StgTRecHeader));
  SET_HDR (result, &stg_TREC_HEADER_info, CCS_SYSTEM);
  result -> next_trec = NO_TREC;
  result -> state = TREC_ACTIVE;
  result -> wait_queue = (StgClosure *)END_STM_WATCH_QUEUE;

  return result;
}

/*......................................................................*/

// Allocation / deallocation functions that retain per-capability lists
// of closures that can be re-used

// These freelist operations update GC-managed links; keep non-moving barriers
// in sync with pointer overwrites.

static StgTVarWatchQueue *alloc_stg_tvar_watch_queue(Capability *cap,
                                                     StgTSO *tso,
                                                     StgTVar *tvar,
                                                     StgClosure *expected,
                                                     StgTVarWatchQueue *next_tso) {
  StgTVarWatchQueue *result = NULL;
  if (cap -> free_tvar_watch_queues == END_STM_WATCH_QUEUE) {
    result = new_stg_tvar_watch_queue(cap, tso, tvar, expected, next_tso);
  } else {
    result = cap -> free_tvar_watch_queues;
    IF_NONMOVING_WRITE_BARRIER_ENABLED {
      updateRemembSetPushClosure(cap, (StgClosure *)cap->free_tvar_watch_queues);
    }
    cap -> free_tvar_watch_queues = result -> next_queue_entry;
    result -> closure = (StgClosure *)tso;
    result -> tvar = tvar;
    result -> expected = expected;
    result -> next_tso_queue_entry = next_tso;
    result -> next_queue_entry = END_STM_WATCH_QUEUE;
    result -> prev_queue_entry = END_STM_WATCH_QUEUE;
  }
  return result;
}

static void free_stg_tvar_watch_queue(Capability *cap,
                                      StgTVarWatchQueue *wq) {
#if defined(REUSE_MEMORY)
  // H-1: do NOT zero the traced pointer fields (tvar/expected/closure/
  // next_tso_queue_entry). Under the nonmoving collector a concurrent mark may
  // already have this entry (still reachable via trec->wait_queue) in its SATB
  // snapshot; nulling expected without pushing the old value would let the
  // snapshot it still needs be reclaimed, while the blocked transaction's
  // revalidation path (validate_and_lock_registered) still reads q->expected --
  // a use-after-free. The whole freelist is dropped wholesale by stmPreGCHook,
  // so zeroing buys no GC-safety anyway. We only repurpose next_queue_entry as
  // the freelist link, barriering its old value.
  IF_NONMOVING_WRITE_BARRIER_ENABLED {
    updateRemembSetPushClosure(cap, (StgClosure *)wq->next_queue_entry);
    updateRemembSetPushClosure(cap, (StgClosure *)cap->free_tvar_watch_queues);
  }
  wq -> next_queue_entry = cap -> free_tvar_watch_queues;
  cap -> free_tvar_watch_queues = wq;
#endif
}

static StgTRecHeader *alloc_stg_trec_header(Capability *cap) {
  StgTRecHeader *result = NULL;
  if (cap -> free_trec_headers == NO_TREC) {
    result = new_stg_trec_header(cap);
  } else {
    result = cap -> free_trec_headers;
    IF_NONMOVING_WRITE_BARRIER_ENABLED {
      updateRemembSetPushClosure(cap, (StgClosure *)cap->free_trec_headers);
      updateRemembSetPushClosure(cap, (StgClosure *)result->next_trec);
    }
    cap -> free_trec_headers = result -> next_trec;
    result -> next_trec = NO_TREC;
    result -> state = TREC_ACTIVE;
  }
  result -> wait_queue = (StgClosure *)END_STM_WATCH_QUEUE;
  return result;
}

static void free_stg_trec_header(Capability *cap,
                                 StgTRecHeader *trec) {
  trec -> wait_queue = (StgClosure *)END_STM_WATCH_QUEUE;
#if defined(REUSE_MEMORY)
  IF_NONMOVING_WRITE_BARRIER_ENABLED {
    updateRemembSetPushClosure(cap, (StgClosure *)trec->next_trec);
    updateRemembSetPushClosure(cap, (StgClosure *)cap->free_trec_headers);
  }
  trec -> next_trec = cap -> free_trec_headers;
  cap -> free_trec_headers = trec;
#endif
}

/*......................................................................*/

/*......................................................................*/

/*......................................................................*/

/*......................................................................*/

static inline StgTVarWatchQueue *trec_wait_list(StgTRecHeader *trec) {
  return (StgTVarWatchQueue *)trec->wait_queue;
}

// M-1: in-place permutation of a traced SmallMutArrPtrs is invisible to the
// nonmoving collector's SATB snapshot unless every overwritten slot's old value
// is pushed to the update remembered set first. recordClosureMutated (run by the
// callers after sorting) only schedules a generational rescan; it does not retain
// the pre-snapshot pointers. So before permuting, push every slot of all three
// arrays. This is conservative (it pushes survivors too) but correct and only
// runs when the nonmoving collector is active.
static void barrier_log_arrays(Capability *cap,
                               StgSmallMutArrPtrs *tvars,
                               StgSmallMutArrPtrs *expected,
                               StgSmallMutArrPtrs *newvals,
                               StgWord len) {
  IF_NONMOVING_WRITE_BARRIER_ENABLED {
    for (StgWord i = 0; i < len; i++) {
      updateRemembSetPushClosure(cap, tvars->payload[i]);
      updateRemembSetPushClosure(cap, expected->payload[i]);
      if (newvals != NULL) {
        updateRemembSetPushClosure(cap, newvals->payload[i]);
      }
    }
  }
}

// L-2: insertion sort is O(n^2) worst case, stacked on the O(n^2) log build,
// inside the commit critical section. It is kept because it is fast for the tiny
// logs typical of STM and needs no auxiliary tvar_id. If large transactions ever
// dominate, sort an index permutation with an O(n log n) sort instead.
static void sort_log_arrays(StgSmallMutArrPtrs *tvars,
                            StgSmallMutArrPtrs *expected,
                            StgSmallMutArrPtrs *newvals,
                            StgWord len) {
  if (len < 2) {
    return;
  }

  for (StgWord i = 1; i < len; i++) {
    StgClosure *key_tvar = tvars->payload[i];
    StgClosure *key_expected = expected->payload[i];
    StgClosure *key_newval = newvals->payload[i];
    StgWord j = i;
    while (j > 0 && (StgWord)tvars->payload[j - 1] > (StgWord)key_tvar) {
      tvars->payload[j] = tvars->payload[j - 1];
      expected->payload[j] = expected->payload[j - 1];
      newvals->payload[j] = newvals->payload[j - 1];
      j--;
    }
    tvars->payload[j] = key_tvar;
    expected->payload[j] = key_expected;
    newvals->payload[j] = key_newval;
  }
}

static void unlock_log_prefix(Capability *cap,
                              StgTRecHeader *trec,
                              StgSmallMutArrPtrs *tvars,
                              StgSmallMutArrPtrs *expected,
                              StgSmallMutArrPtrs *newvals,
                              StgWord upto,
                              StgBool acquire_all) {
  for (StgWord i = 0; i < upto; i++) {
    StgClosure *expected_val = expected->payload[i];
    StgClosure *new_val = newvals->payload[i];
    StgBool is_update = (new_val != expected_val);
    if (acquire_all || is_update) {
      StgTVar *s = (StgTVar *)tvars->payload[i];
      unlock_tvar(cap, trec, s, expected_val, true);
    }
  }
}

static StgBool validate_and_lock_log(Capability *cap,
                                     StgTRecHeader *trec,
                                     StgSmallMutArrPtrs *tvars,
                                     StgSmallMutArrPtrs *expected,
                                     StgSmallMutArrPtrs *newvals,
                                     StgWord len,
                                     StgBool acquire_all,
                                     StgInt *num_updates) {
#if !defined(STM_FG_LOCKS)
  (void)num_updates;
#endif
  if (shake()) {
    TRACE("%p : shake, pretending log is invalid when it may not be", trec);
    return false;
  }

  for (StgWord i = 0; i < len; i++) {
    StgTVar *s = (StgTVar *)tvars->payload[i];
    StgClosure *expected_val = expected->payload[i];
    StgClosure *new_val = newvals->payload[i];
    StgBool is_update = (new_val != expected_val);
    if (acquire_all || is_update) {
      if (!cond_lock_tvar(cap, trec, s, expected_val)) {
        unlock_log_prefix(cap, trec, tvars, expected, newvals, i, acquire_all);
        return false;
      }
    } else {
      // Read-only entry: verify the value is still what we expect, no lock.
      if (ACQUIRE_LOAD(&s->current_value) != expected_val) {
        unlock_log_prefix(cap, trec, tvars, expected, newvals, i, acquire_all);
        return false;
      }
#if defined(STM_FG_LOCKS)
      // Snapshot num_updates between two value checks so a concurrent commit
      // landing here is caught; check_read_only_log re-checks against it.
      num_updates[i] = SEQ_CST_LOAD(&s->num_updates);
      if (ACQUIRE_LOAD(&s->current_value) != expected_val) {
        unlock_log_prefix(cap, trec, tvars, expected, newvals, i, acquire_all);
        return false;
      }
#endif
    }
  }

  return true;
}

static StgBool check_read_only_log(StgSmallMutArrPtrs *tvars,
                                   StgSmallMutArrPtrs *expected,
                                   StgSmallMutArrPtrs *newvals,
                                   StgWord len,
                                   StgInt *num_updates) {
#if !defined(STM_FG_LOCKS)
  (void)tvars;
  (void)expected;
  (void)newvals;
  (void)len;
  (void)num_updates;
#endif
#if defined(STM_FG_LOCKS)
  for (StgWord i = 0; i < len; i++) {
    StgClosure *expected_val = expected->payload[i];
    StgClosure *new_val = newvals->payload[i];
    if (new_val == expected_val) {
      StgTVar *s = (StgTVar *)tvars->payload[i];
      StgClosure *current_value = ACQUIRE_LOAD(&s->current_value);
      StgInt seen_updates = SEQ_CST_LOAD(&s->num_updates);
      if (current_value != expected_val || seen_updates != num_updates[i]) {
        return false;
      }
    }
  }
#endif
  return true;
}

static void commit_log_entries(Capability *cap,
                               StgTRecHeader *trec,
                               StgSmallMutArrPtrs *tvars,
                               StgSmallMutArrPtrs *expected,
                               StgSmallMutArrPtrs *newvals,
                               StgWord len,
                               StgBool acquire_all) {
  // L-1: invariant -- every committer that changes current_value MUST also bump
  // num_updates (the is_update branch below does both, atomically w.r.t. the
  // lock held on s). The read-phase validation (check_read_only_log /
  // stmValidateLog) relies on this: a no-op write (new_val == expected_val) is
  // suppressed here precisely so that an unchanged TVar's num_updates is never
  // perturbed, keeping the double-load + num_updates recheck sound. Do not bump
  // num_updates without writing current_value, or vice versa.
  for (StgWord i = 0; i < len; i++) {
    StgTVar *s = (StgTVar *)tvars->payload[i];
    StgClosure *expected_val = expected->payload[i];
    StgClosure *new_val = newvals->payload[i];
    StgBool is_update = (new_val != expected_val);
    if (is_update) {
      unpark_waiters_on(cap, s);
#if defined(STM_FG_LOCKS)
      NONATOMIC_ADD(&s->num_updates, 1);
#endif
      unlock_tvar(cap, trec, s, new_val, true);
    } else if (acquire_all) {
      // No-op entry (new == expected). Unlock if we hold the lock because
      // acquire_all locked every slot above. In the read-phase mode (acquire_all
      // == false) a non-update slot is left untouched.
      unlock_tvar(cap, trec, s, expected_val, true);
    }
  }
}

static void unlock_registered_prefix(Capability *cap,
                                     StgTRecHeader *trec,
                                     StgTVarWatchQueue *head,
                                     StgTVarWatchQueue *stop) {
  for (StgTVarWatchQueue *q = head; q != stop; q = q->next_tso_queue_entry) {
    unlock_tvar(cap, trec, q->tvar, q->expected, true);
  }
}

static void unlock_registered_all(Capability *cap,
                                  StgTRecHeader *trec,
                                  StgTVarWatchQueue *head) {
  unlock_registered_prefix(cap, trec, head, END_STM_WATCH_QUEUE);
}

static StgBool validate_and_lock_registered(Capability *cap,
                                            StgTRecHeader *trec,
                                            StgTVarWatchQueue *head) {
  if (shake()) {
    TRACE("%p : shake, pretending registrations are invalid when they may not be", trec);
    return false;
  }

  for (StgTVarWatchQueue *q = head; q != END_STM_WATCH_QUEUE; q = q->next_tso_queue_entry) {
    if (!cond_lock_tvar(cap, trec, q->tvar, q->expected)) {
      unlock_registered_prefix(cap, trec, head, q);
      return false;
    }
  }

  return true;
}

static void remove_wait_queue_entries_from_list(Capability *cap,
                                                StgTRecHeader *trec) {
  StgTVarWatchQueue *q = trec_wait_list(trec);
  while (q != END_STM_WATCH_QUEUE) {
    StgTVarWatchQueue *next = q->next_tso_queue_entry;
    StgTVar *s = q->tvar;
    StgClosure *saw = lock_tvar(cap, trec, s);
    StgTVarWatchQueue *pq = q->prev_queue_entry;
    StgTVarWatchQueue *nq = q->next_queue_entry;
    if (nq != END_STM_WATCH_QUEUE) {
      nq->prev_queue_entry = pq;
    }
    if (pq != END_STM_WATCH_QUEUE) {
      pq->next_queue_entry = nq;
    } else {
      ASSERT(ACQUIRE_LOAD(&s->first_watch_queue_entry) == q);
      RELEASE_STORE(&s->first_watch_queue_entry, nq);
      dirty_TVAR(cap, s, (StgClosure *)q);
    }
    free_stg_tvar_watch_queue(cap, q);
    unlock_tvar(cap, trec, s, saw, false);
    q = next;
  }
  trec->wait_queue = (StgClosure *)END_STM_WATCH_QUEUE;
}


/************************************************************************/

void stmPreGCHook (Capability *cap) {
  TRACE("stmPreGCHook");
  cap->free_tvar_watch_queues = END_STM_WATCH_QUEUE;
  cap->free_trec_headers = NO_TREC;
}

/************************************************************************/

// check_read_only relies on version numbers held in TVars' "num_updates"
// fields not wrapping around while a transaction is committed. The version
// number is incremented each time an update is committed to the TVar. On
// 32-bit builds we maintain a shared count on the maximum number of commit
// operations that may occur and check that this has not increased by more
// than 2^32 during a commit.

#define TOKEN_BATCH_SIZE 1024

#if defined(THREADED_RTS) && WORD_SIZE_IN_BITS < 64

static volatile StgInt64 max_commits = 0;

static volatile StgWord token_locked = false;

#if WORD_SIZE_IN_BITS < 64
// Only the 32-bit commit-overflow check (in stmCommitLog) reads max_commits.
static StgInt64 getMaxCommits(void) {
  return RELAXED_LOAD(&max_commits);
}
#endif

static void getTokenBatch(Capability *cap) {
  while (cas((void *)&token_locked, false, true) == true) { /* nothing */ }
  NONATOMIC_ADD(&max_commits, TOKEN_BATCH_SIZE);
  TRACE("%p : cap got token batch, max_commits=%" FMT_Int64, cap, RELAXED_LOAD(&max_commits));
  cap -> transaction_tokens = TOKEN_BATCH_SIZE;
  RELEASE_STORE(&token_locked, false);
}

static void getToken(Capability *cap) {
  if (cap -> transaction_tokens == 0) {
    getTokenBatch(cap);
  }
  cap -> transaction_tokens --;
}
#else
#if WORD_SIZE_IN_BITS < 64
static StgInt64 getMaxCommits(void) {
    return 0;
}
#endif

static void getToken(Capability *cap STG_UNUSED) {
  // Nothing
}
#endif

/*......................................................................*/

StgTRecHeader *stmStartTransaction(Capability *cap,
                                   StgTRecHeader *outer) {
  StgTRecHeader *t;
  TRACE("%p : stmStartTransaction with %d tokens",
        outer,
        cap -> transaction_tokens);

  getToken(cap);

  ASSERT(outer == NO_TREC);
  t = alloc_stg_trec_header(cap);
  TRACE("%p : stmStartTransaction()=%p", outer, t);
  return t;
}

/*......................................................................*/

void stmAbortTransaction(Capability *cap,
                         StgTRecHeader *trec) {
  TRACE("%p : stmAbortTransaction", trec);
  ASSERT(trec != NO_TREC);
  ASSERT((trec -> state == TREC_ACTIVE) ||
         (trec -> state == TREC_WAITING) ||
         (trec -> state == TREC_CONDEMNED));

  TRACE("%p : aborting transaction", trec);
  if (trec_wait_list(trec) != END_STM_WATCH_QUEUE) {
    TRACE("%p : stmAbortTransaction clearing registrations", trec);
    remove_wait_queue_entries_from_list(cap, trec);
  }

  trec -> state = TREC_CONDEMNED;
  TRACE("%p : stmAbortTransaction done", trec);
}

/*......................................................................*/

void stmFreeTransaction(Capability *cap,
                        StgTRecHeader *trec) {
  TRACE("%p : stmFreeTransaction", trec);
  ASSERT(trec != NO_TREC);
  ASSERT((trec -> state == TREC_ACTIVE) ||
         (trec -> state == TREC_CONDEMNED));

  free_stg_trec_header(cap, trec);

  TRACE("%p : stmFreeTransaction done", trec);
}

/*......................................................................*/

void stmCondemnTransaction(Capability *cap,
                           StgTRecHeader *trec) {
  TRACE("%p : stmCondemnTransaction", trec);
  ASSERT(trec != NO_TREC);
  ASSERT((trec -> state == TREC_ACTIVE) ||
         (trec -> state == TREC_WAITING) ||
         (trec -> state == TREC_CONDEMNED));

  if (trec_wait_list(trec) != END_STM_WATCH_QUEUE) {
    TRACE("%p : stmCondemnTransaction clearing registrations", trec);
    remove_wait_queue_entries_from_list(cap, trec);
  }
  trec -> state = TREC_CONDEMNED;

  TRACE("%p : stmCondemnTransaction done", trec);
}

/*......................................................................*/

StgInt stmCommitLog(Capability *cap,
                    StgTSO *tso,
                    StgSmallMutArrPtrs *tvars,
                    StgSmallMutArrPtrs *expected,
                    StgSmallMutArrPtrs *newvals,
                    StgInt len) {
  StgTRecHeader *trec = tso->trec;
  TRACE("%p : stmCommitLog()", trec);
  ASSERT(trec != NO_TREC);
  ASSERT(trec -> next_trec == NO_TREC);
  ASSERT((trec -> state == TREC_ACTIVE) ||
         (trec -> state == TREC_CONDEMNED));
  if (trec->state == TREC_CONDEMNED) {
    if (trec_wait_list(trec) != END_STM_WATCH_QUEUE) {
      remove_wait_queue_entries_from_list(cap, trec);
    }
    TRACE("%p : stmCommitLog()=%d", trec, 0);
    return 1;
  }

  StgWord count = (StgWord)len;
  // M-1: barrier the old slot values before the in-place permutation, then
  // recordClosureMutated for the generational rescan after.
  barrier_log_arrays(cap, tvars, expected, newvals, count);
  sort_log_arrays(tvars, expected, newvals, count);
  recordClosureMutated(cap, (StgClosure *)tvars);
  recordClosureMutated(cap, (StgClosure *)expected);
  recordClosureMutated(cap, (StgClosure *)newvals);

#if WORD_SIZE_IN_BITS < 64
  StgInt64 max_commits_at_start = getMaxCommits();
#endif
  StgBool acquire_all = (!config_use_read_phase);

  StgInt *num_updates = NULL;
#if defined(STM_FG_LOCKS)
  StgInt num_updates_buf[STM_NUM_UPDATES_STACK_LIMIT];
  if (config_use_read_phase && count > 0) {
    if (count <= (StgWord)STM_NUM_UPDATES_STACK_LIMIT) {
      num_updates = num_updates_buf;
    } else {
      num_updates = stgMallocBytes(sizeof(StgInt) * count,
                                   "stmCommitLog num_updates");
    }
  }
#endif

  bool result = validate_and_lock_log(cap,
                                      trec,
                                      tvars,
                                      expected,
                                      newvals,
                                      count,
                                      acquire_all,
                                      num_updates);

  if (result) {
    if (config_use_read_phase) {
      if (!check_read_only_log(tvars, expected, newvals, count, num_updates)) {
        result = false;
      } else {
#if WORD_SIZE_IN_BITS < 64
        StgInt64 max_commits_at_end = getMaxCommits();
        StgInt64 max_concurrent_commits =
          ((max_commits_at_end - max_commits_at_start) +
           (getNumCapabilities() * TOKEN_BATCH_SIZE));
        if ((max_concurrent_commits >> 32) > 0) {
          TRACE("STM - Max commit number exceeded");
          result = false;
        }
#endif
        if (result && shake()) {
          TRACE("STM - Max commit number exceeded");
          result = false;
        }
      }
    }

    if (result) {
      commit_log_entries(cap, trec, tvars, expected, newvals, count, acquire_all);
    } else {
      unlock_log_prefix(cap, trec, tvars, expected, newvals, count, acquire_all);
    }
  }

#if defined(STM_FG_LOCKS)
  if (num_updates != NULL && num_updates != num_updates_buf) {
    stgFree(num_updates);
  }
#endif

  if (result) {
    TRACE("%p : stmCommitLog()=%d", trec, result);
    return 0;
  }

  TRACE("%p : stmCommitLog()=%d", trec, result);
  return 1;
}

/*......................................................................*/

// validate# : lock-free, address-independent revalidation of a logged read set.
//
// Given parallel arrays of tvars and the expected values observed for them, plus
// a length, check that every TVar's current value is still pointer-equal to its
// expected value. Returns 0 if the read set is still consistent, 1 if any TVar
// has changed (the transaction is a zombie and must restart). Takes no locks and
// performs no writes; it is the read branch of validate_and_lock_log with the
// STM_FG_LOCKS double-load + num_updates recheck, but it never CASes.
StgInt stmValidateLog(Capability *cap STG_UNUSED,
                      StgTSO *tso,
                      StgSmallMutArrPtrs *tvars,
                      StgSmallMutArrPtrs *expected,
                      StgInt len) {
  StgTRecHeader *trec = tso->trec;
  TRACE("%p : stmValidateLog(%" FMT_Word ")", trec, (StgWord)len);
  ASSERT(trec != NO_TREC);

  if (shake()) {
    TRACE("%p : shake, pretending log is invalid when it may not be", trec);
    return 1;
  }

  for (StgInt i = 0; i < len; i++) {
    StgTVar *s = (StgTVar *)tvars->payload[i];
    StgClosure *expected_val = expected->payload[i];
#if defined(STM_FG_LOCKS)
    // Double-load + num_updates recheck so we never conclude "consistent" off a
    // value seen mid-commit (a TREC_HEADER lock stamp or a value about to be
    // re-checked by num_updates). If a concurrent committer holds the lock, the
    // stamp differs from expected_val and we report a conflict.
    StgClosure *current_value = ACQUIRE_LOAD(&s->current_value);
    StgInt seen_updates = SEQ_CST_LOAD(&s->num_updates);
    StgClosure *current_value2 = ACQUIRE_LOAD(&s->current_value);
    if (current_value != expected_val ||
        current_value2 != expected_val ||
        seen_updates != SEQ_CST_LOAD(&s->num_updates)) {
      TRACE("%p : stmValidateLog()=1 (i=%" FMT_Word ")", trec, (StgWord)i);
      return 1;
    }
#else
    StgClosure *current_value = ACQUIRE_LOAD(&s->current_value);
    if (current_value != expected_val) {
      TRACE("%p : stmValidateLog()=1 (i=%" FMT_Word ")", trec, (StgWord)i);
      return 1;
    }
#endif
  }

  TRACE("%p : stmValidateLog()=0", trec);
  return 0;
}

/*......................................................................*/

// readMany# : batch-read (and optimistically validate) a statically-known
// fragment read set in one RTS pass.
//
// tvars holds the fragment's PRead TVars; this fills results with each TVar's
// current value and expected with the same snapshot (for later commit/
// validation), over indices [0, len). Returns 0 if the whole batch was read from
// a mutually-consistent snapshot, 1 if a concurrent commit was observed
// mid-batch (caller should restart the fragment). Reads only; takes no locks.
StgInt stmReadMany(Capability *cap,
                   StgTSO *tso,
                   StgSmallMutArrPtrs *tvars,
                   StgSmallMutArrPtrs *results,
                   StgSmallMutArrPtrs *expected,
                   StgInt len) {
  StgTRecHeader *trec = tso->trec;
  TRACE("%p : stmReadMany(%" FMT_Word ")", trec, (StgWord)len);
  ASSERT(trec != NO_TREC);

  // We overwrite traced pointer slots of results/expected; push their old values
  // for the nonmoving SATB snapshot before the fill.
  barrier_log_arrays(cap, results, expected, NULL, (StgWord)len);

  for (StgInt i = 0; i < len; i++) {
    StgTVar *s = (StgTVar *)tvars->payload[i];
    StgClosure *r;
#if defined(STM_FG_LOCKS)
    // Spin past a TREC_HEADER lock stamp (a concurrent committer) as lock_tvar's
    // inner loop does, but without CASing, then double-load to detect a commit
    // that landed between the read and the num_updates snapshot.
    StgInt seen_updates;
    for (;;) {
      const StgInfoTable *info;
      do {
        r = ACQUIRE_LOAD(&s->current_value);
        info = GET_INFO(UNTAG_CLOSURE(r));
      } while (info == &stg_TREC_HEADER_info);
      seen_updates = SEQ_CST_LOAD(&s->num_updates);
      if (ACQUIRE_LOAD(&s->current_value) == r &&
          SEQ_CST_LOAD(&s->num_updates) == seen_updates) {
        break;
      }
    }
#else
    r = ACQUIRE_LOAD(&s->current_value);
#endif
    results->payload[i] = r;
    expected->payload[i] = r;
  }

  recordClosureMutated(cap, (StgClosure *)results);
  recordClosureMutated(cap, (StgClosure *)expected);

  // Always 0: each TVar above is read with an individually-stable double-load,
  // but we deliberately do not detect a cross-batch tear (a commit landing
  // between two of the reads). That is caught downstream by validate# before the
  // next continuation and by the commit-time check; an extra re-snapshot pass
  // here would only narrow the zombie window, not change correctness.
  TRACE("%p : stmReadMany()=0", trec);
  return 0;
}

/*......................................................................*/

static void register_wait(Capability *cap,
                          StgTSO *tso,
                          StgTRecHeader *trec,
                          StgTVar *tvar,
                          StgClosure *expected) {
  for (StgTVarWatchQueue *q = trec_wait_list(trec);
       q != END_STM_WATCH_QUEUE;
       q = q->next_tso_queue_entry) {
    if (q->tvar == tvar) {
      // H-2: overwriting a traced MUT_PRIM field that may already be in the
      // nonmoving snapshot; push the old expected value first.
      IF_NONMOVING_WRITE_BARRIER_ENABLED {
        updateRemembSetPushClosure(cap, q->expected);
      }
      q->expected = expected;
      return;
    }
  }

  StgTVarWatchQueue *q =
    alloc_stg_tvar_watch_queue(cap, tso, tvar, expected, trec_wait_list(trec));

  StgClosure *saw = lock_tvar(cap, trec, tvar);
  StgTVarWatchQueue *fq = ACQUIRE_LOAD(&tvar->first_watch_queue_entry);
  q->next_queue_entry = fq;
  q->prev_queue_entry = END_STM_WATCH_QUEUE;
  if (fq != END_STM_WATCH_QUEUE) {
    fq->prev_queue_entry = q;
  }
  RELEASE_STORE(&tvar->first_watch_queue_entry, q);
  IF_NONMOVING_WRITE_BARRIER_ENABLED {
    updateRemembSetPushClosure(cap, (StgClosure *)q);
  }
  dirty_TVAR(cap, tvar, (StgClosure *)fq);
  unlock_tvar(cap, trec, tvar, saw, false);

  trec->wait_queue = (StgClosure *)q;
}

void stmRegisterLogRange(Capability *cap,
                         StgTSO *tso,
                         StgSmallMutArrPtrs *tvars,
                         StgSmallMutArrPtrs *expected,
                         StgInt start,
                         StgInt end) {
  StgTRecHeader *trec = tso->trec;
  TRACE("%p : stmRegisterLogRange()", trec);
  ASSERT(trec != NO_TREC);
  ASSERT(trec->next_trec == NO_TREC);
  ASSERT((trec->state == TREC_ACTIVE) ||
         (trec->state == TREC_CONDEMNED));

  if (trec->state == TREC_CONDEMNED) {
    return;
  }

  for (StgInt i = start; i < end; i++) {
    StgTVar *tvar = (StgTVar *)tvars->payload[i];
    StgClosure *exp = expected->payload[i];
    register_wait(cap, tso, trec, tvar, exp);
  }
}

StgBool stmBlockOnRegistered(Capability *cap, StgTSO *tso) {
  StgTRecHeader *trec = tso->trec;

  TRACE("%p : stmBlockOnRegistered(%p)", trec, tso);
  ASSERT(trec != NO_TREC);
  ASSERT(trec->next_trec == NO_TREC);
  ASSERT((trec->state == TREC_ACTIVE) ||
         (trec->state == TREC_CONDEMNED));

  if (trec->state == TREC_CONDEMNED) {
    return false;
  }

  StgTVarWatchQueue *head = trec_wait_list(trec);
  if (!validate_and_lock_registered(cap, trec, head)) {
    return false;
  }

  park_tso(tso);
  trec->state = TREC_WAITING;
  unlock_registered_all(cap, trec, head);

  return true;
}

void stmClearRegistrations(Capability *cap, StgTSO *tso) {
  StgTRecHeader *trec = tso->trec;

  TRACE("%p : stmClearRegistrations(%p)", trec, tso);
  if (trec == NO_TREC) {
    return;
  }

  if (trec_wait_list(trec) != END_STM_WATCH_QUEUE) {
    remove_wait_queue_entries_from_list(cap, trec);
  }

  if (trec->state == TREC_WAITING) {
    trec->state = TREC_ACTIVE;
  }
}

/*......................................................................*/
