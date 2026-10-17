import Leanux.Env

/-! Literal factors of the current timer-wheel environment loops. Both factors
retain the product runner state, actual native WireGuard lifts, record order,
guards, and stops. The removed raw-expiry scan is not an executable alternative
to the wheel's bucket and enqueue ordering. -/
namespace Leanux.Proofs.WG.Environment
open Leanux Leanux.WG Leanux.Env

def runTimersSource (jPass : UInt64) : Leanux.M Bool := do
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

theorem runTimersSource_eq (jPass : UInt64) :
    runTimersSource jPass = Env.runTimers jPass := rfl

def runTimersPlaceholderSource (jHi : UInt64) : Leanux.M Unit := do
  modifyWG fun w => { w with queuedThisCall := [] }
  if (← getWG).dev.isNone then return   -- no device, no timers
  -- the filter's own loop (review item 7): one turn per pending timer at most
  let pending := (← getDev).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let some (pid, t, _) := TimerWheel.nextDue (← getDev) jHi | break
    delTimer pid t
    runTimerSection (← timerWorker t) (WG.timerCallback pid t)
  runCryptWorkers
  runSendWorkers
  for _ in [0:(← getDev).clearWorkQueue.length + 1] do
    if (← getDev).clearWorkQueue.isEmpty then break
    runOneClearWorker

theorem runTimersPlaceholderSource_eq (jHi : UInt64) :
    runTimersPlaceholderSource jHi = Env.runTimersPlaceholder jHi := rfl

end Leanux.Proofs.WG.Environment
