import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalEffectsSource
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsProjection

/-! Exact same-run projections for the new native disposal callbacks. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Effects
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
variable (ρ : E → Option F) {g : TimerEffects.Ops (WGPrefix E)} {t : TimerEffects.Ops (WGPrefix F)}
  (h : TimerEffects.Ops.Projects ρ g t)
  (rg : Option PeerId → WGPrefix E Unit) (rt : Option PeerId → WGPrefix F Unit)
  (hr : ∀ peer, StateProjectsPrefix ρ id (rg peer) (rt peer))

include h hr in
theorem queued_projects (pid : PeerId) (retry : Bool) :
    StateProjectsPrefix ρ id (queuedWith g rg pid retry) (queuedWith t rt pid retry) := by
  unfold queuedWith
  repeat' first | exact hr _ | timer_effects_project h ρ

include h hr in
theorem retransmit_projects (pg : PeerId → WGPrefix E Unit) (pt : PeerId → WGPrefix F Unit)
    (hp : ∀ pid, StateProjectsPrefix ρ id (pg pid) (pt pid)) (pid : PeerId) :
    StateProjectsPrefix ρ id (retransmitWith g rg pg pid) (retransmitWith t rt pt pid) := by
  unfold retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | exact hp _
    | (maintenance_head TimerEffects.modifyWith; exact TimerEffects.modify_projects ρ h _ _ _ _)
    | (maintenance_head queuedWith; exact queued_projects ρ h rg rt hr _ _)
    | timer_effects_project h ρ

include h hr in
theorem newHandshake_projects (pid : PeerId) :
    StateProjectsPrefix ρ id (newHandshakeWith g rg pid) (newHandshakeWith t rt pid) := by
  unfold newHandshakeWith
  repeat' first
    | (maintenance_head queuedWith; exact queued_projects ρ h rg rt hr _ _)
    | timer_effects_project h ρ

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Effects
