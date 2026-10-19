import Leanux.Proofs.WG.RetirementSecurity.HolderReceivePacket

/-! Original handshake worker selection composes key-credit transport through
the actual ring pop, packet processing and queue-length decrement. The
incoming independently proved allocation/session support stays explicit. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderReceive
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits
set_option maxHeartbeats 600000

theorem pop (ring : PtrRing (List UInt8 × SkbSource)) :
    Preserves (Ready temporary) (modifyDev (popHandshakeQueue ring)) := by
  apply combine
  · exact HolderResponse.points (erasesStatePrefix_lift _) (allocationReceiveQueue.pop ring)
      (ownership_modifyDev _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl))
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.modifyDevice)
    all_goals intro d; rfl

theorem decrement : Preserves (Ready temporary) (modifyDev decHandshakeQueue) := by
  apply combine
  · exact HolderResponse.points (erasesStatePrefix_lift _) allocationReceiveQueue.decrement
      (ownership_modifyDev _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl))
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.modifyDevice)
    all_goals intro d; rfl

theorem step : Preserves (Ready temporary) WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head getDev; exact store getDev_sameWGStore)
    | (rx_retention_head modifyDev; first | exact decrement | exact pop _)
    | (rx_retention_head receiveHandshakePacket; exact receive _ _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.RetirementSecurity.HolderReceive
