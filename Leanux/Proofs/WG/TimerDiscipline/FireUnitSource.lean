import Leanux.Proofs.WG.TimerDiscipline.WheelDispatchSource
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

def timerDispatchPrefix_variant (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) : Leanux.M Unit := do
  let expected ← timerWorker t
  if w != expected then
    throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}")
  if let some u ← peekUnit w then
    match (← getWG).timerUnits.find? (·.1 == u) with
    | some (_, pid', t') =>
      if pid' != pid || t' != t then
        throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}")
    | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
  if let some b := step then
    if b != we.bucketExpiry then requireStepComplete b

def fireWheelSelected (w : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) : Leanux.M Unit := do
  delTimer pid timer
  modifyWG fun s => {s with timerPassStep := some we.bucketExpiry}
  runTimerSection w (WG.timerCallback pid timer)
  modifyWG fun s => {s with timerPassStep := none}

theorem throw_bind_timer {α β : Type} (e : Stop) (f : α → Leanux.M β) :
    ((throw e : Leanux.M α) >>= f) = throw e := rfl

theorem unsupported_bind_timer {α β : Type} (message : String) (f : α → Leanux.M β) :
    ((unsupported message : Leanux.M α) >>= f) = unsupported message := by
  rfl

theorem fireTimer_source (w : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) :
    timerDispatchUnit_variant w pid timer we step =
      (do timerDispatchPrefix_variant w pid timer we step
          fireWheelSelected w pid timer we) := by
  simp only [timerDispatchUnit_variant, timerDispatchPrefix_variant, fireWheelSelected, bind_assoc]
  repeat' first
    | rfl
    | (split <;> try simp_all only [bind_assoc, pure_bind, throw_bind_timer])
    | (congr 1; funext x)
end Leanux.Proofs.WG.TimerDiscipline
