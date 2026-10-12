import Leanux.WG.Device
import Leanux.WG.Data
import Leanux.Env.IpStack

/-!
# Deferred units: dispatch sections and the scheduler's choices

Split out of `Leanux/Env.lean` at the interface commit (docs/2026-10-11-interface.md).
Owned by W4+W7's stream B (docs/2026-10-06-w4-w7-transmit-bulk.md, sections
12 and 15): `batch` (from E-B's `flood`), `napiSoftirq` with the per-peer
poll list and `net_rx_action`'s repoll, the `condResched` generalization and
the generic phase-1 nesting detector land here; `Env.lean` keeps the hooks
(`batch`, the worker runners `runCryptWorkers`, `runSendWorkers`,
`runDecryptWorker`, `napiSoftirq`, `napiIrqExit`, which deliver over the
loopback and so stay with the fixture). This file holds what every runner
shares: a unit's section (`runWorker`), the section sites (`sectionOf`) and
the recorded `cond_resched` switches (`condResched`, `SWITCH_DEPTH`).
-/

namespace Leanux.Env
open Leanux Leanux.WG

/-- A deferred unit's run. The kernel (the `net-choice` profile since the
    D1 sprint) opens a dispatch section per dispatch of a function in the
    armed set (`harness/linux.py`, `DISPATCH_SYMBOLS`); its start and
    stop records bracket it in the choice stream, so the order in which the
    kernel ran deferred units is checked rather than assumed.

    A worker that switched away at a `cond_resched` (`condResched`) resumes
    when the kernel's scheduler picks it again, which may be after workers
    the mirror cannot run first: its own callers, preempted further up the
    mirror's call stack. The mirror runs the rest of such a worker at once
    and leaves its stop pending; the stop's record is consumed where Linux
    recorded it (`skipAmbient`), and an operation ends with none pending
    (`Runner.executeTrace`). This assumes the resumed rests commute: they
    may read no hidden input (a read out of order is a mismatch) and touch
    no state the others read. On the modeled paths each rest is a worker's
    final empty ring or queue poll. -/
def runWorker (w : Worker) (body : M Unit) (pid : Option Nat := none) : M Unit := do
  _ ← hidden (.sectionStart w)
  -- whether this run switched away
  modify fun s => { s with yieldedWorkers := s.yieldedWorkers.filter (· != w.index),
                           openWorkers := s.openWorkers ++ [(w.index, pid)] }
  -- W7 stream H (13.2 (ii)): a NET_RX section's steps carry its ordinal in
  -- the operation; a softirq never nests in a softirq, so the ordinal is
  -- cleared at its end
  if w == .netRx then
    modify fun s => { s with netRxSections := s.netRxSections + 1, netRxSection := s.netRxSections + 1 }
  body
  if w == .netRx then modify fun s => { s with netRxSection := 0 }
  modify fun s => { s with openWorkers := s.openWorkers.dropLast }
  let stop := (HiddenSite.sectionStop w).info.id
  let deferred := (← get).yieldedWorkers.contains w.index && (← peekHiddenSite).isSome
    && (← peekHiddenSite) != some stop
  if deferred then modify fun s => { s with pendingStops := s.pendingStops ++ [stop] }
  else _ ← hidden (.sectionStop w)

/-- An item of `wg_batch` (W7, section 5.5): a datagram the fixture's sender
    submits in one `io_uring_enter`, to wg0's port (`inject`) or into wg0
    (`xmit`, as `wg_xmit`'s packet). -/
inductive BatchItem where
  | inject (family port : Nat) (message : List UInt8)
  | xmit (family addr : Nat) (payload : List UInt8) (opts : XmitOpts)
  deriving Repr

/-- Whether an open worker still has queued items it would process when
    it resumes (5.4): the encrypt ring, the tx work queue or a tx worker's
    own queue with a head it can send, the decrypt ring, the handshake
    queue. The test names no unit pair. -/
def queuedWork (w : Nat) (pid : Option Nat) : M Bool := do
  let d ← getDev
  if w == Worker.encryptWorker.index then return !d.encryptQueue.empty
  if w == Worker.decryptWorker.index then return !d.decryptQueue.empty
  if w == Worker.receiveWorker.index then return !d.handshakeQueue.isEmpty
  if w == Worker.txWorker.index then
    if !d.txWorkQueue.isEmpty then return true
    let some pid := pid | return false
    let p ← getPeer pid
    for item in p.txQueue.all do
      if let some id := item.head? then
        if (← getTxSkb id).state != .uncrypted then return true
    return false
  return false

/-- The worker whose section a record starts or stops, with `true` for a
    start; `none` for other records and for `net_rx_action`, a softirq,
    which the environment runs where its records say: nested where it is
    raised, or (D2) in ksoftirqd after a worker's switch. -/
def sectionOf (site : Nat) : Option (Worker × Bool) :=
  [Worker.sendWorker, .receiveWorker, .encryptWorker, .txWorker, .decryptWorker].findSome? fun w =>
    if site == (HiddenSite.sectionStart w).info.id then some (w, true)
    else if site == (HiddenSite.sectionStop w).info.id then some (w, false)
    else none

/-- `need_resched()` and `cond_resched()` in worker `self`, on the kernel's
    one CPU (`CONFIG_PREEMPT_NONE`): whether the kernel switched away, having
    run here what it ran. A scheduling choice, recorded: the kernel writes a
    resched record when `__cond_resched` is about to schedule. Then each
    following record that starts a crypt worker with queued work is that
    worker's run here (and so on, for what it switched to in turn). What the
    kernel ran that has no section (another task) leaves no other record;
    a worker the mirror cannot run here (a caller further up its stack)
    resumes later (`runWorker`). `fuel` bounds the nesting: each level is a
    worker run.

    A NET_RX section the records place at the yield is the NAPI poll a
    pending `napi_schedule` raised, which ksoftirqd ran when the worker
    gave up the CPU (D2's order (a), docs/2026-10-04-d2-data-plane.md
    section 5) before the kernel ran the crypt worker whose start follows:
    it runs first, by the NET_RX rules (`runNetRx`, `Env.napiSoftirq`), and
    the switch to that worker is still taken (W7, docs/2026-10-06-w4-w7-
    transmit-bulk.md 17.14: `w7_mixed`). Any other record at the yield
    stays with the resuming worker, whose next read it must be, else a
    hidden mismatch. -/
def condResched : Nat → Worker → M Unit → M Unit → M Bool
  | 0, _, _, _ => invariant "worker switches nested too deep"
  | fuel + 1, self, runDecrypt, runNetRx => do
    let some site := self.resched? | invariant s!"{self.symbol} has no cond_resched"
    if (← peekHiddenSite) != some site.info.id then return false
    _ ← hidden site
    -- W7 (5.3): any of the encrypt, tx and decrypt workers whose start is
    -- next and whose queue is non-empty runs here; the tx worker is the one
    -- the dispatch record names (docs/2026-10-11-dispatch-order.md)
    for _ in [0:16] do
      match (← peekHiddenSite).bind sectionOf with
      | some (.encryptWorker, true) =>
        if (← getDev).encryptQueue.empty then break   -- not runnable: the record mismatches later
        runWorker .encryptWorker (WG.encryptWorker checksumHelp (condResched fuel .encryptWorker runDecrypt runNetRx))
      | some (.txWorker, true) =>
        let d ← getDev
        let some headPid := d.txWorkQueue.head? | break
        let pid ← match ← peekUnit .txWorker with
          | some u => resolveUnit .txWorker u d.txWorkQueue
          | none => pure headPid
        modifyDev fun d => { d with txWorkQueue := d.txWorkQueue.erase pid }
        runWorker .txWorker (WG.txWorker pid (condResched fuel .txWorker runDecrypt runNetRx)) (some pid)
      | some (.decryptWorker, true) =>
        if (← getDev).decryptQueue.empty then break
        runDecrypt
      | _ =>
        -- the NAPI poll at the yield (the docstring): pending, with its
        -- section's start next; `runNetRx` consumes it, or the record is
        -- left to the caller
        let netRx := (HiddenSite.sectionStart .netRx).info.id
        if (← peekHiddenSite) == some netRx && (← getDev).peers.toList.any (·.2.napiScheduled) then
          runNetRx
          if (← peekHiddenSite) == some netRx then break
        else break
    -- the loop ends at a record it does not run; one it could run is a
    -- run beyond its bound
    match (← peekHiddenSite).bind sectionOf with
    | some (.encryptWorker, true) | some (.txWorker, true) | some (.decryptWorker, true) =>
      let d ← getDev
      if !d.encryptQueue.empty || !d.txWorkQueue.isEmpty || !d.decryptQueue.empty then
        invariant "more worker runs at one cond_resched than the loop allows"
    | _ => pure ()
    -- W7 phase 1 (5.4): a nested unit that yields while an outer open
    -- worker still has queued items. The mirror runs the nested unit to its
    -- end inside the outer's call, so the outer would see its queue only
    -- afterwards, while Linux may resume the outer first: the rests do not
    -- commute, and the mirror's stack order is not Linux's. Fail-closed.
    -- Phase 2 (17.15) is not built on this representation: it needs
    -- suspended activations resumed by the recorded schedule.
    let stack := (← get).openWorkers
    if stack.length ≥ 2 then
      for (w, pid) in stack.dropLast do
        if ← queuedWork w pid then
          unsupported "a worker yielded below an open worker with queued work (the mirror's stack order)"
    modify fun s => { s with yieldedWorkers := s.yieldedWorkers ++ [self.index] }
    return true

/-- The bound on `condResched`'s nesting: a worker kind runs at most once
    per level on the modeled paths. -/
def SWITCH_DEPTH : Nat := 4

end Leanux.Env
