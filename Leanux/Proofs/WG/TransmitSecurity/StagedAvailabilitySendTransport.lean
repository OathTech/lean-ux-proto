import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilitySendFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityHandshakeTransport
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! Full native send-work transport combines history provenance with the
separate native staged-queue frame. No selected-work hypothesis is needed
merely to preserve staged origins. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem history_emit (event : Event) (quiet : allocation? event = none) : Driver.StateHistorySafe Safe (emitStatePrefix event) :=
  StatePrefixEnsures.emit event (fun _ _ _ before => before.emit (quiet_event quiet))
    (fun _ _ _ before => before.emit (quiet_event quiet))

theorem history_receipt (body : WGPrefix Event α) (safe : Driver.StateHistorySafe Safe body)
    (record : WGRunWitness α → Event) (quiet : ∀ r, allocation? (record r) = none) :
    Driver.StateHistorySafe Safe (receiptWGObserved body record) := by
  unfold receiptWGObserved
  exact StatePrefixEnsures.bind safe.captureWGObserved (fun r =>
    StatePrefixEnsures.bind (history_emit (record r) (quiet r)) (fun _ => Driver.History.state_pure _))

theorem history_scope (cause : Cause) (body : WGPrefix Event α) (safe : Driver.StateHistorySafe Safe body) :
    Driver.StateHistorySafe Safe (CausalScope.scope Event.scope cause body) :=
  CausalScope.scope_preserves Event.scope cause body (fun _ _ _ before => before)
    (fun event _ _ _ before => before.emit (quiet_event (event := .scope event) rfl)) safe

theorem protocol_send_history (pid : PeerId) (bytes : List UInt8) :
    Driver.StateHistorySafe Safe (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) :=
  ProtocolSocket.observed_history Safe Event.protocolSocket scope?
    (fun h args receipt before _ => before.emit
      (quiet_event (event := .protocolSocket ⟨CausalScope.current scope? h,args,receipt⟩) rfl)) pid bytes

theorem initiated_history (pid : PeerId) : Driver.StateHistorySafe Safe (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  repeat' effect_history_step effects_history

private theorem send_body (pid : PeerId) : Driver.StateHistorySafe Safe
    (SendExchange.workerWith (SendEffects.withEffects
      (ExchangeJoint.sendOps Event.exchange (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal? (ProtocolSender.sendOps Event.protocolSocket scope?))) effects) pid) := by
  unfold SendExchange.workerWith SendExchange.sendWith
  simp only [SendEffects.withEffects,ExchangeJoint.sendOps,StagedDisposal.Decoration.send,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (driver_history_head StagedDisposal.Decoration.release; exact disposal_history _)
    | (driver_history_head ProtocolSocket.observed; exact protocol_send_history _ _)
    | (driver_history_head receiptWGObserved; exact history_receipt _ (Driver.History.state_lift _) _ (fun _ => rfl))
    | (driver_history_head TimerEffects.traversalWith; exact Driver.effects_traversal_history effects_history _)
    | (driver_history_head TimerEffects.initiatedWith; exact initiated_history _)
    | driver_state_history_step

private theorem flushed_body (pid : PeerId) : Driver.StateHistorySafe Safe
    (SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith
      (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal? (ProtocolSender.sendOps Event.protocolSocket scope?))) effects)) pid) := by
  unfold SendExchange.flushedWith SendExchange.afterTakeWith
  repeat' first
    | (driver_history_head SendExchange.workerWith; exact send_body _)
    | driver_state_history_step

theorem flushed_send_history (pid : PeerId) : Driver.StateHistorySafe Safe (flushedSend pid) := by
  intro w a h before
  exact history_scope (.sendWork pid (CausalSources.sendEntry pid w)) _ (flushed_body pid) w a h before

theorem projected_native_erases {action : WGPrefix Event α} {native : WG.M α}
    (projected : StateProjectsPrefix ρ id action (liftWGPrefix native)) : ErasesStatePrefix action native := by
  intro w a h
  have equal := congrArg Prod.fst (projected w a h)
  change (native.run w).run a = (runWGPrefix action w a h).1.map id at equal
  simpa only [Except.map_id,id_eq,runWGPrefix,runStatePrefix] using equal.symm

theorem flushed_send_observed (pid : PeerId) : StateSafe (flushedSend pid) :=
  state_history (flushed_send_history pid) (projected_native_erases (flushed_projects pid))
    (fun _ => Native.flushed_send pid) (flushed_noallocation pid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
