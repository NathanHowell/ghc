//#OPTIONS: CPP

// software transactional memory

#ifdef GHCJS_TRACE_STM
function h$logStm() { if(arguments.length == 1) {
                         h$log("stm: " + arguments[0]);
                       } else {
                         h$log.apply(h$log,arguments);
                       }
                     }
#define TRACE_STM(args...) h$logStm(args)
#else
#define TRACE_STM(args...)
#endif


var h$TVarN = 0;
/** @constructor */
function h$TVar(v) {
    TRACE_STM("creating TVar, value: " + h$collectProps(v))
    this.val        = v;           // current value
    this.blocked    = new h$Set(); // threads that get woken up if this TVar is updated
    this.m          = 0;           // gc mark
    this._key       = ++h$TVarN;   // for storing in h$Map/h$Set
#ifdef GHCJS_DEBUG_ALLOC
    h$debugAlloc_notifyAlloc(this);
#endif
}

/** @constructor */
function h$TVarsWaiting() {
  this.tvars = new h$Map();  // TVar -> expected
#ifdef GHCJS_DEBUG_ALLOC
  h$debugAlloc_notifyAlloc(this);
#endif
}

function h$stmWaiting(thread) {
  var waiting = thread.stmWaiting;
  if(waiting === undefined || waiting === null) {
    waiting = new h$TVarsWaiting();
    thread.stmWaiting = waiting;
  }
  return waiting;
}

function h$stmClearRegistrationsThread(thread) {
  var waiting = thread.stmWaiting;
  if(waiting === undefined || waiting === null) return;
  var tv, i = waiting.tvars.iter();
  while((tv = i.next()) !== null) {
    tv.blocked.remove(thread);
  }
  waiting.tvars = new h$Map();
  thread.stmWaiting = null;
}

function h$atomically(o) {
  h$p2(o, h$atomically_e);
  return h$stmStartTransaction(o);
}

function h$stmStartTransaction(o) {
  TRACE_STM("starting transaction: " + h$collectProps(o))
  h$r1 = o;
  return h$ap_1_0_fast();
}

function h$stmCommitLog(tvars, expected, newvals, len) {
  var blockedThreads = new h$Set();

  for (var i = 0; i < len; i++) {
    if (tvars[i].val !== expected[i]) {
      return 1;
    }
  }

  for (var j = 0; j < len; j++) {
    h$stmCommitTVar(tvars[j], newvals[j], blockedThreads);
  }

  var thread, iter = blockedThreads.iter();
  while ((thread = iter.next()) !== null) {
    if(thread.status === THREAD_BLOCKED && thread.blockedOn instanceof h$TVarsWaiting) {
      h$stmClearRegistrationsThread(thread);
      thread.sp += 2;
      thread.stack[thread.sp-1] = 0;
      thread.stack[thread.sp]   = h$return;
      h$wakeupThread(thread);
    }
  }

  return 0;
}

function h$registerLogRange(tvars, expected, start, end) {
  for (var i = start; i < end; i++) {
    h$registerWait(tvars[i], expected[i]);
  }
}

function h$registerWait(tvar, expected) {
  var waiting = h$stmWaiting(h$currentThread);
  var regs = waiting.tvars;
  var seen = regs.has(tvar);
  regs.put(tvar, expected);
  if(seen) return;
  tvar.blocked.add(h$currentThread);
}

function h$blockOnRegistered() {
  var waiting = h$stmWaiting(h$currentThread);
  var regs = waiting.tvars;
  var tv, i = regs.iter();
  while((tv = i.next()) !== null) {
    if(tv.val !== regs.get(tv)) {
      h$stmClearRegistrationsThread(h$currentThread);
      h$r1 = 0;
      return h$rs();
    }
  }
  h$currentThread.interruptible = true;
  return h$blockThread(h$currentThread, waiting);
}

function h$clearRegistrations() {
  h$stmClearRegistrationsThread(h$currentThread);
}

function h$stmWait(tvars, expected, queues, len) {
  // unwind stack to h$atomically_e frame
  while (h$sp > 0) {
    var f = h$stack[h$sp];
    if (f === h$atomically_e) {
      break;
    }
    var size;
    if (f === h$ap_gen) {
      size = ((h$stack[h$sp-1] >> 8) + 2);
    } else {
      var tag = f.gtag;
      if (tag < 0) { // dynamic size
        size = h$stack[h$sp-1];
      } else {
        size = (tag & 0xff) + 1;
      }
    }
    h$sp -= size;
  }

  if (h$sp <= 0 || h$stack[h$sp] !== h$atomically_e) {
    throw "h$stmWait: wait outside a transaction";
  }

  for (var i = 0; i < len; i++) {
    if (tvars[i].val !== expected[i]) {
      return h$stmStartTransaction(h$stack[h$sp - 1]);
    }
  }

  h$stmClearRegistrationsThread(h$currentThread);
  var waiting = h$stmWaiting(h$currentThread);

  for (var j = 0; j < len; j++) {
    h$registerWait(tvars[j], expected[j]);
  }

  h$currentThread.interruptible = true;
  h$p2(waiting, h$stmResumeRetry_e);
  return h$blockThread(h$currentThread, waiting);
}

function h$newTVar(v) {
  return new h$TVar(v);
}

function h$readTVarIO(tv) {
  return tv.val;
}

function h$sameTVar(tv1, tv2) {
  return tv1 === tv2;
}

function h$stmCommitTVar(tv, v, threads) {
    TRACE_STM("committing tvar: " + tv._key + " " + (v === tv.val))
    if(v !== tv.val) {
        var thr, iter = tv.blocked.iter();
        while((thr = iter.next()) !== null) {
            if(thr.status === THREAD_BLOCKED && thr.blockedOn instanceof h$TVarsWaiting) {
                threads.add(thr);
            }
        }
        tv.val = v;
    }
}

// remove the thread from the queues of the TVars in s
function h$stmRemoveBlockedThread(s, thread) {
    if(s === null || s === undefined) return;
    if(thread.stmWaiting === s) {
      h$stmClearRegistrationsThread(thread);
      return;
    }
    var tv, i = s.tvars.iter();
    while((tv = i.next()) !== null) {
      tv.blocked.remove(thread);
    }
    s.tvars = new h$Map();
}
