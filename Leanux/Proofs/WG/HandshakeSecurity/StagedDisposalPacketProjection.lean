import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalPacketSource
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalEffectsProjection

/-! Exact projection of receive-side rekey repayment, with unchanged
packet/timer control flow and retained stopped histories. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PacketSource
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects TimerEffects
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
variable (ρ : E → Option F) {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}
  (h : Ops.Projects ρ g t)
  (rg : Option PeerId → WGPrefix E Unit) (rt : Option PeerId → WGPrefix F Unit)
  (hr : ∀ peer, StateProjectsPrefix ρ id (rg peer) (rt peer))

include h hr in
theorem freshReceive_projects (pid : PeerId) :
    StateProjectsPrefix ρ id (freshReceiveWith g rg pid) (freshReceiveWith t rt pid) := by
  unfold freshReceiveWith
  repeat' first | with_reducible exact Effects.queued_projects ρ h rg rt hr _ _ | timer_effects_project h ρ

include h hr in
theorem prepare_projects (pid : PeerId) (pkt : RxPacket) :
    StateProjectsPrefix ρ id (prepareWith g rg pid pkt) (prepareWith t rt pid pkt) := by
  unfold prepareWith
  repeat' first
    | with_reducible exact freshReceive_projects ρ h rg rt hr _
    | with_reducible exact traversal_projects ρ h _
    | with_reducible exact dataReceived_projects ρ h _
    | timer_effects_project h ρ

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PacketSource
