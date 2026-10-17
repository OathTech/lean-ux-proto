import Leanux.Proofs.WG.TimerDiscipline.RetryEligibilitySource
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.TimerDiscipline.FireUnitSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env
/-- The actual callback section, retaining its callback's queue-inspection bit. -/
def observedRetransmitSection (pid : PeerId) : Leanux.M (Option Bool) := do
  modifyAmbient fun s => {s with fired := s.fired.push Worker.timerRetransmit.symbol}
  let _ ← hidden (.sectionStart .timerRetransmit)
  let inspected ← liftWG (observedRetransmitHandshake pid)
  let _ ← hidden (.sectionStop .timerRetransmit)
  pure inspected

def observedFireSelected (pid : PeerId) (we : WheelEntry) : Leanux.M (Option Bool) := do
  liftWG (delTimer pid .retransmitHandshake)
  modifyWG fun s => {s with timerPassStep := some we.bucketExpiry}
  let inspected ← observedRetransmitSection pid
  modifyWG fun s => {s with timerPassStep := none}
  pure inspected

theorem observedRetransmitSection_erase (pid : PeerId) :
    (do let _ ← observedRetransmitSection pid; pure ()) =
      runTimerSection .timerRetransmit (liftWG (expiredRetransmitHandshake pid)) := by
  have callback : (do let _ ← liftWG (observedRetransmitHandshake pid); pure ()) =
      liftWG (expiredRetransmitHandshake pid) := by
    rw [← observedRetransmitHandshake_erase, liftWG_bind_variant]
    rfl
  rw [runTimerSection, runWorker]
  simp only [Worker.timer?, Option.isNone_some, Bool.false_eq_true, ite_false]
  change _ = (do
    modifyAmbient fun s => {s with fired := s.fired.push Worker.timerRetransmit.symbol}
    let _ ← hidden (.sectionStart .timerRetransmit)
    liftWG (expiredRetransmitHandshake pid)
    let _ ← hidden (.sectionStop .timerRetransmit)
    pure ())
  rw [← callback]
  simp only [observedRetransmitSection, bind_assoc, pure_bind]

theorem observedFireSelected_erase (pid : PeerId) (we : WheelEntry) :
    (do let _ ← observedFireSelected pid we; pure ()) =
      fireWheelSelected .timerRetransmit pid .retransmitHandshake we := by
  have factor : fireWheelSelected .timerRetransmit pid .retransmitHandshake we = (do
      liftWG (delTimer pid .retransmitHandshake)
      modifyWG fun s => {s with timerPassStep := some we.bucketExpiry}
      runTimerSection .timerRetransmit (liftWG (expiredRetransmitHandshake pid))
      modifyWG fun s => {s with timerPassStep := none}) := rfl
  rw [factor, ← observedRetransmitSection_erase]
  simp only [observedFireSelected, bind_assoc, pure_bind]
  simp
end Leanux.Proofs.WG.TimerDiscipline
