import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionQuiet

/-! The actual callback retains earlier delivery certificates; its emitted
metadata does not add a delivery boundary. Native emission accounting remains
a separate source contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem send_body (pid : PeerId) : Driver.StateHistorySafe Safe
    (SendExchange.workerWith (SendEffects.withEffects
      (ExchangeJoint.sendOps Event.exchange (ProtocolSender.sendOps Event.protocolSocket scope?)) effects) pid) := by
  unfold SendExchange.workerWith SendExchange.sendWith
  simp only [SendEffects.withEffects,ExchangeJoint.sendOps,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head receiptWGObserved; exact receipt_quiet _ (Driver.History.state_lift _) _ (fun _ => rfl))
    | (driver_history_head TimerEffects.traversalWith; exact Driver.effects_traversal_history effects_safe _)
    | (driver_history_head TimerEffects.initiatedWith; exact initiated _)
    | driver_state_history_step

private theorem flushed_body (pid : PeerId) : Driver.StateHistorySafe Safe
    (SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith
      (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange (ProtocolSender.sendOps Event.protocolSocket scope?)) effects)) pid) := by
  unfold SendExchange.flushedWith SendExchange.afterTakeWith
  repeat' first
    | (driver_history_head ProtocolSocket.observed; exact protocol_send _ _)
    | (driver_history_head CookieSocket.observed; exact cookie_send _ _ _)
    | (driver_history_head SendExchange.workerWith; exact send_body _)
    | driver_state_history_step

theorem flushed_send (pid : PeerId) : Driver.StateHistorySafe Safe (flushedSend pid) := by
  intro w a h hi
  exact state_scope (.sendWork pid (CausalSources.sendEntry pid w)) (fun _ => rfl) _ (flushed_body pid) w a h hi

theorem send_worker : Driver.ProductHistorySafe Safe (Driver.sendWorkerObserved hooks) := by
  unfold Driver.sendWorkerObserved SendExchange.oneWith
  exact Driver.History.product_bind (Driver.History.product_lift _) (fun pid =>
    Driver.History.product_state (flushed_send pid))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
