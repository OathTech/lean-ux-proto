import Leanux.Proofs.WG.TransmitSecurity.StagedTimerOriginFrames
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory

/-! Native timer effects preserve staged provenance; their receipts are quiet
for staged selection, independently of their separate causal authorization. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000

private theorem history_emit (event : Event) (quiet : Quiet event) :
    Driver.StateHistorySafe Safe (emitStatePrefix event) :=
  StatePrefixEnsures.emit event
    (fun h _ _ before => before.emit (checked_quiet event quiet h))
    (fun h _ _ before => before.emit (checked_quiet event quiet h))

private theorem history_receipt (action : WG.M α) (record : WGRunWitness α → Event)
    (quiet : ∀ r, Quiet (record r)) :
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
      (fun _ => True.intro) w a h before
  append := by
    intro pid w a h before
    exact history_receipt (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
      (fun r => .queued ⟨CausalScope.current scope? h,pid,r⟩)
      (fun _ => True.intro) w a h before

theorem modify_timer_observed (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe (TimerEffects.modifyWith effects site pid timer delay) :=
  state_history (Driver.effects_modify_history effects_history site pid timer delay)
    (TimerEffects.modify_erases (CausalEffects.ops_erases scope? Event.armed Event.queued) site pid timer delay)
    (fun _ => Native.modify_timer site pid timer delay)

theorem traversal_observed (pid : PeerId) : StateSafe (TimerEffects.traversalWith effects pid) :=
  state_history (Driver.effects_traversal_history effects_history pid)
    (TimerEffects.traversal_erases (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
    (fun _ => Native.traversal pid)

theorem data_received_observed (pid : PeerId) : StateSafe (TimerEffects.dataReceivedWith effects pid) :=
  state_history (Driver.effects_dataReceived_history effects_history pid)
    (TimerEffects.dataReceived_erases (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
    (fun _ => Native.data_received pid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
