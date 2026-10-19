import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDisposal
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.SendCallerContracts

/-! Ordered emission accounting through selected and directly drained native
handshake-send work. Dequeue and worker bookkeeping add no datagrams; the
actual protocol sender accounts at each socket append. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing HandshakeSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem send_body (pid : PeerId) : StateSafe
    (SendExchange.workerWith (SendEffects.withEffects
      (ExchangeJoint.sendOps Event.exchange (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal?
        (ProtocolSender.sendOps Event.protocolSocket scope?))) effects) pid) := by
  unfold SendExchange.workerWith SendExchange.sendWith
  simp only [SendEffects.withEffects,ExchangeJoint.sendOps,StagedDisposal.Decoration.send,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (emission_head receiptWGObserved; refine state_receipt _ ?_ _ (fun _ => rfl))
    | (emission_native_head createInitiation; exact state_native _ (EmissionFrames.create_initiation _))
    | (emission_head TimerEffects.traversalWith; exact traversal _)
    | (emission_head TimerEffects.initiatedWith; exact initiated _)
    | (emission_head StagedDisposal.Decoration.release; exact peer_release _)
    | emission_handshake_native
    | emission_step

private theorem after_take (pid : PeerId) : StateSafe
    (SendExchange.afterTakeWith liftWGPrefix (SendExchange.workerWith
      (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange
        (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal?
        (ProtocolSender.sendOps Event.protocolSocket scope?))) effects)) pid) := by
  unfold SendExchange.afterTakeWith
  repeat' first
    | (emission_head SendExchange.workerWith; exact send_body _)
    | (emission_head StagedDisposal.Decoration.release; exact peer_release _)
    | emission_handshake_native
    | emission_step

theorem flushed_send (pid : PeerId) : StateSafe (flushedSend pid) := by
  intro w a h hi
  apply state_scope (.sendWork pid (CausalSources.sendEntry pid w)) _ ?_ w a h hi
  apply state_bind
  · emission_native
  · intro _
    exact after_take pid

theorem send_worker : ProductSafe (TransmitSecurity.Driver.sendWorkerObserved hooks) :=
  SendCallers.one_preserves Inv (fun _ => True) (fun _ _ _ => True.intro) flushedSend
    (fun pid => (flushed_send pid).consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
