import Leanux.Env

/-! Literal original timer continuation after the complete saved-map scan.
No proof imports or alternative execution are introduced into the mirror. -/
namespace Leanux.Proofs.WG.Environment
open Leanux Leanux.WG

def fireTimerAfterScan (worker : Worker) (t : PeerTimer) (jHi : UInt64) (due : List PeerId) : M Unit := do
  let named ← match ← peekUnit worker with
    | some u =>
      match (← get).timerUnits.find? (·.1 == u) with
      | some (_, pid, t') =>
        if t' != t then throw (.hidden s!"a section of {worker.symbol} for another timer of peer {pid}")
        pure (some pid)
      | none => throw (.hidden s!"a section of {worker.symbol} for a timer the mirror never armed ({u})")
    | none => pure none
  match named with
  | some pid =>
    if !due.contains pid then
      throw (.hidden s!"a section of {worker.symbol} for peer {pid}, whose timer is not pending with expires before jiffies {jHi}")
    delTimer pid t
    Env.runTimerSection worker (WG.timerCallback pid t)
  | none =>
    match due with
    | [pid] =>
      delTimer pid t
      Env.runTimerSection worker (WG.timerCallback pid t)
    | [] => throw (.hidden s!"a section of {worker.symbol}, but no peer's timer is pending with expires before jiffies {jHi}")
    | _ => unsupported s!"several peers' timers for {worker.symbol} due in one pass (their order)"

def fireTimerSource (worker : Worker) (jHi : UInt64) : M Unit := do
  let some t := worker.timer? | invariant s!"{worker.symbol} is not a timer callback"
  let d ← getDev
  let due := d.peerList.filter fun pid =>
    match d.peers.get? pid >>= (·.timer t) with
    | some e => timeBefore e jHi | none => false
  fireTimerAfterScan worker t jHi due

theorem fireTimerSource_eq (worker : Worker) (jHi : UInt64) :
    fireTimerSource worker jHi = Env.fireTimer worker jHi := rfl

/-- The original pure earliest-entry fold, shared to avoid independently generated
matcher constants in the two observations of the placeholder loop. -/
def firstDue (due : List (UInt64 × PeerId × PeerTimer)) : Option (UInt64 × PeerId × PeerTimer) :=
  due.foldl (fun acc c => match acc with
    | some a => if timeBefore c.1 a.1 then some c else some a
    | none => some c) none

theorem firstDue_eq (due : List (UInt64 × PeerId × PeerTimer)) : firstDue due =
    due.foldl (fun acc c => match acc with
      | some a => if timeBefore c.1 a.1 then some c else some a
      | none => some c) none := rfl

def dueEntries (d : Device) (jHi : UInt64) : List (UInt64 × PeerId × PeerTimer) := d.peerList.flatMap fun pid =>
      match d.peers.get? pid with
      | some p => PeerTimer.all.filterMap fun t => (p.timer t).bind fun e => if timeBefore e jHi then some (e, pid, t) else none
      | none => []

def runTimersPlaceholderSource (jHi : UInt64) : M Unit := do
  modify fun w => { w with queuedThisCall := [] }
  if (← getK).wg.isNone then return   -- L: no wg0, no timers [AGENT, int-dl merge]
  -- the filter's own loop (review item 7): one turn per pending timer at most
  let pending := (← getDev).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let d ← getDev
    let due := dueEntries d jHi
    let first := firstDue due
    let some (_, pid, t) := first | break
    delTimer pid t
    Env.runTimerSection (← Env.timerWorker t) (WG.timerCallback pid t)
  Env.runCryptWorkers
  Env.runSendWorkers
  for _ in [0:(← getDev).clearWorkQueue.length + 1] do
    if (← getDev).clearWorkQueue.isEmpty then break
    Env.runOneClearWorker

theorem runTimersPlaceholderSource_eq (jHi : UInt64) :
    runTimersPlaceholderSource jHi = Env.runTimersPlaceholder jHi := rfl

end Leanux.Proofs.WG.Environment
