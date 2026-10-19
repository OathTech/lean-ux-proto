import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageEffects

/-! Scheduled and directly drained handshake sends enter their actual queued
work scope before effects. The initialized queue-occurrence theorem supplies its
parent; this file establishes only coverage at that native source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem send_body (pid : PeerId) (live : frames ≠ []) : StateAt frames
    (SendExchange.workerWith (SendEffects.withEffects
      (ExchangeJoint.sendOps Event.exchange SendEffects.native) effects) pid) := by
  unfold SendExchange.workerWith SendExchange.sendWith
  simp only [SendEffects.withEffects,ExchangeJoint.sendOps,SendEffects.native]
  repeat' first
    | (coverage_head receiptWGObserved; exact state_receipt _ (state_lift _) _ (fun _ => rfl)
        (fun _ impossible => impossible.elim))
    | (coverage_head TimerEffects.traversalWith; exact traversal _ live)
    | (coverage_head TimerEffects.initiatedWith; exact initiated _ live)
    | coverage_state_step

private theorem flushed_body (pid : PeerId) (live : frames ≠ []) : StateAt frames
    (SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith
      (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange SendEffects.native) effects)) pid) := by
  unfold SendExchange.flushedWith SendExchange.afterTakeWith
  repeat' first
    | (coverage_head SendExchange.workerWith; exact send_body _ live)
    | coverage_state_step

theorem flushed_send (pid : PeerId) : StateAt frames (flushedSend pid) := by
  intro w a h ready
  exact state_scope (.sendWork pid (CausalSources.sendEntry pid w)) _
    (fun _ live => flushed_body pid live) frames w a h ready

theorem send_worker : ProductAt frames (Driver.sendWorkerObserved hooks) := by
  unfold Driver.sendWorkerObserved SendExchange.oneWith
  exact product_bind (product_lift _) (fun pid => product_state _ (flushed_send pid))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
