import Leanux.Proofs.WG.TransmitSecurity.StagedSendFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityEffects

/-! Handshake send work neither allocates transport batches nor spends staged
birth credits. Its actual peer release may remove a resident queue. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity

theorem Native.flushed_send (pid : PeerId) : Preserves (Inv h) (runFlushedSendWork pid) :=
  frame (PacketOrigins.epoch_ring ((RetirementSecurity.OccurrenceDeferred.flushed_send_wire pid).factor Prod.fst))
    (Staged.flushed_send pid)

theorem flushed_noallocation (pid : PeerId) : StateHistoryFrame allocation? (flushedSend pid) := by
  have projected := SendEffects.flushed_native_projects allocation? Event.scope (fun _ => rfl)
    (ExchangeJoint.send_ignored allocation? Event.exchange (fun _ => rfl) _ _
      (ProtocolSender.send_projects allocation? Event.protocolSocket scope? (fun _ => rfl)))
    (CausalEffects.ops_projects scope? Event.armed Event.queued allocation? (fun _ => rfl) (fun _ => rfl)) pid
  intro w a history
  exact (congrArg Prod.snd (projected w a history)).symm

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
