import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityAdapters
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory

/-! Timer-effect histories cannot spend a staged birth credit. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

private theorem history_emit (event : Event) (quiet : allocation? event = none) :
    Driver.StateHistorySafe Safe (emitStatePrefix event) :=
  StatePrefixEnsures.emit event
    (fun _ _ _ before => before.emit (quiet_event quiet))
    (fun _ _ _ before => before.emit (quiet_event quiet))

private theorem history_receipt (action : WG.M α) (record : WGRunWitness α → Event)
    (quiet : ∀ r, allocation? (record r) = none) :
    Driver.StateHistorySafe Safe (receiptWGObserved (liftWGPrefix action) record) := by
  unfold receiptWGObserved
  exact StatePrefixEnsures.bind (Driver.History.state_lift action).captureWGObserved
    (fun r => StatePrefixEnsures.bind (history_emit (record r) (quiet r))
      (fun _ => Driver.History.state_pure _))

theorem effects_history : Driver.EffectsHistory Safe effects where
  step := Driver.History.state_lift
  arm := by
    intro pid timer delay caller w a h before
    exact history_receipt (armTimer pid timer delay caller)
      (fun r => .armed ⟨CausalScope.current scope? h,pid,timer,delay,caller,r⟩)
      (fun _ => rfl) w a h before
  append := by
    intro pid w a h before
    exact history_receipt (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
      (fun r => .queued ⟨CausalScope.current scope? h,pid,r⟩)
      (fun _ => rfl) w a h before


end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
