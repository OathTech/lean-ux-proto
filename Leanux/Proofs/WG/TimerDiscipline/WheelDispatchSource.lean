import Leanux.Env
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env
/-! Local source-factor variant of campaign 1's Logged.timerDispatchUnit.
The actual Product dispatcher keeps guards, errors, wheel metadata and its
post-callback step reset. No due-peer compatibility dispatcher is introduced. -/
def timerDispatchUnit_variant (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) : Leanux.M Unit := do
  let expected ← timerWorker t
  if w != expected then
    throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}")
  -- dispatch order (docs/2026-10-11-dispatch-order.md): the timer the
  -- section names, by the address its arm record carried
  if let some u ← peekUnit w then
    match (← getWG).timerUnits.find? (·.1 == u) with
    | some (_, pid', t') =>
      if pid' != pid || t' != t then
        throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}")
    | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
  if let some b := step then
    if b != we.bucketExpiry then requireStepComplete b
  delTimer pid t
  modifyWG fun s => { s with timerPassStep := some we.bucketExpiry }
  runTimerSection w (WG.timerCallback pid t)
  modifyWG fun s => { s with timerPassStep := none }

def runTimersWheelSource (jPass : UInt64) : Leanux.M Bool := do
  modifyWG fun w => { w with queuedThisCall := [] }   -- the guest slept
  -- L: without wg0 (bare fixture, or after wg_delete) no WireGuard timer
  -- exists; a timer section in the records stays unconsumed and mismatches
  if (← getWG).dev.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  let mut step : Option UInt64 := none
  -- record-driven (review item 7): every turn consumes a section or breaks
  for _ in [0:(← recordBudget)] do
    let some site ← peekNextSite | break
    let d ← getDev
    if let some w := timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          requireStepComplete b
          step := none
        if d.clearWorkQueue.isEmpty then break
        runOneClearWorker
      else
        let some (pid, t, we) := TimerWheel.nextDue d jPass
          | throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}")
        timerDispatchUnit_variant w pid t we step
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        requireStepComplete b
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then runOneSendWorker
      else
        -- the crypt work a timer queued, as the records order it, and a crypt
        -- activation the records resume after a section (`schedule`)
        runCryptWorkers
        if (← peekNextSite) == some site then break
  if let some b := step then requireStepComplete b
  if fired then
    deliverSent
    let d ← getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      unsupported "work a timer queued outlived the guest's wait"
  return fired

theorem runTimers_wheel_source (jPass : UInt64) :
    runTimersWheelSource jPass = Env.runTimers jPass := by
  have stopped {α β : Type} (e : Stop) (f : α → Leanux.M β) :
      ((throw e : Leanux.M α) >>= f) = throw e := rfl
  simp only [runTimersWheelSource, Env.runTimers, timerDispatchUnit_variant, bind_assoc, stopped]
  repeat' first
    | rfl
    | split
    | (congr 1; funext x)

  apply congrFun
  rename_i budget
  apply congrArg (fun (body : Nat → (Bool × Option UInt64) → Leanux.M (ForInStep (Bool × Option UInt64))) =>
    forIn ([:budget] : Std.Legacy.Range) (false, none) body)
  funext turn state
  repeat' first
    | rfl
    | (split <;> try simp_all only [bind_assoc])
    | (congr 1; funext x)

end Leanux.Proofs.WG.TimerDiscipline
