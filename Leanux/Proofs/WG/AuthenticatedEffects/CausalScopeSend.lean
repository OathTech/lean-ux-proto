import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeEffects

/-! The native send source restores its incoming lexical stack on
normal completion and retains a well-formed stack on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem send_body (pid : PeerId) : StateSafe
    (SendExchange.workerWith (SendEffects.withEffects
      (ExchangeJoint.sendOps Event.exchange (ProtocolSender.sendOps Event.protocolSocket scope?)) effects) pid) := by
  unfold SendExchange.workerWith SendExchange.sendWith
  simp only [SendEffects.withEffects,ExchangeJoint.sendOps,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (scope_balance_head ProtocolSocket.observed; exact protocol_send _ _)
    | (scope_balance_head CookieSocket.observed; exact cookie_send _ _ _)
    | (scope_balance_head receiptWGObserved; exact state_receipt _ (state_lift _) _ (fun _ => rfl))
    | (scope_balance_head TimerEffects.traversalWith; exact traversal _)
    | (scope_balance_head TimerEffects.initiatedWith; exact initiated _)
    | scope_state_step

private theorem flushed_body (pid : PeerId) : StateSafe
    (SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith
      (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange (ProtocolSender.sendOps Event.protocolSocket scope?)) effects)) pid) := by
  unfold SendExchange.flushedWith SendExchange.afterTakeWith
  repeat' first
    | (scope_balance_head ProtocolSocket.observed; exact protocol_send _ _)
    | (scope_balance_head CookieSocket.observed; exact cookie_send _ _ _)
    | (scope_balance_head SendExchange.workerWith; exact send_body _)
    | scope_state_step

theorem flushed_send (pid : PeerId) : StateSafe (flushedSend pid) := by
  intro frames w a h hi
  exact state_scope (.sendWork pid (CausalSources.sendEntry pid w)) _ (flushed_body pid) frames w a h hi

theorem send_worker : ProductSafe (Driver.sendWorkerObserved hooks) := by
  unfold Driver.sendWorkerObserved SendExchange.oneWith
  exact product_bind (product_lift _) (fun pid =>
    product_state _ (flushed_send pid))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
