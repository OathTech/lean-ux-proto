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
def runWorker (w : Worker) (body : M Unit) : M Unit := do
  _ ← hidden (.sectionStart w)
  -- whether this run switched away
  modify fun s => { s with yieldedWorkers := s.yieldedWorkers.filter (· != w.index) }
  body
  let stop := (HiddenSite.sectionStop w).info.id
  let deferred := (← get).yieldedWorkers.contains w.index && (← peekHiddenSite).isSome
    && (← peekHiddenSite) != some stop
  if deferred then modify fun s => { s with pendingStops := s.pendingStops ++ [stop] }
  else _ ← hidden (.sectionStop w)

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
    worker run. -/
def condResched : Nat → Worker → M Bool
  | 0, _ => invariant "worker switches nested too deep"
  | fuel + 1, self => do
    let some site := self.resched? | invariant s!"{self.symbol} has no cond_resched"
    if (← peekHiddenSite) != some site.info.id then return false
    _ ← hidden site
    for _ in [0:16] do
      match (← peekHiddenSite).bind sectionOf with
      | some (.encryptWorker, true) =>
        if (← getDev).encryptQueue.isEmpty then break   -- not runnable: the record mismatches later
        runWorker .encryptWorker (WG.encryptWorker checksumHelp (condResched fuel .encryptWorker))
      | some (.txWorker, true) =>
        let some pid := (← getDev).txWorkQueue.head? | break
        modifyDev fun d => { d with txWorkQueue := d.txWorkQueue.drop 1 }
        runWorker .txWorker (WG.txWorker pid (condResched fuel .txWorker))
      | _ => break
    -- the loop ends at a record it does not run; one it could run is a
    -- run beyond its bound
    match (← peekHiddenSite).bind sectionOf with
    | some (.encryptWorker, true) | some (.txWorker, true) =>
      if !(← getDev).encryptQueue.isEmpty || !(← getDev).txWorkQueue.isEmpty then
        invariant "more crypt worker runs at one cond_resched than the loop allows"
    | _ => pure ()
    modify fun s => { s with yieldedWorkers := s.yieldedWorkers ++ [self.index] }
    return true

/-- The bound on `condResched`'s nesting: a worker kind runs at most once
    per level on the modeled paths. -/
def SWITCH_DEPTH : Nat := 4

end Leanux.Env
