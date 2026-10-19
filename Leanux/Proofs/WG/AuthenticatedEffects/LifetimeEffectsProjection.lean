import Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffectsSource

/-! Exact lifetime-event projection through the callback-parametric timer and
work-queue helpers, including every retained prefix on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Projects (ρ : E → Option F) (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F)) : Prop where
  step : ∀ {α} (a : WG.M α), StateProjectsPrefix ρ id (g.step a) (t.step a)
  peer : ∀ pid, StateProjectsPrefix ρ id (g.peer pid) (t.peer pid)
  keypair : ∀ kid, StateProjectsPrefix ρ id (g.keypair kid) (t.keypair kid)
  modifyPeer : ∀ pid f, StateProjectsPrefix ρ id (g.modifyPeer pid f) (t.modifyPeer pid f)
  guard : ∀ pid, StateProjectsPrefix ρ id (g.guard pid) (t.guard pid)
  arm : ∀ pid timer delay caller, StateProjectsPrefix ρ id (g.arm pid timer delay caller) (t.arm pid timer delay caller)
  get : ∀ pid, StateProjectsPrefix ρ id (g.get pid) (t.get pid)
  put : ∀ pid, StateProjectsPrefix ρ id (g.put pid) (t.put pid)
  append : ∀ pid, StateProjectsPrefix ρ id (g.append pid) (t.append pid)

macro "lifetime_effects_project " h:ident rho:ident : tactic => `(tactic| first
  | with_reducible exact Ops.Projects.step $h _
  | with_reducible exact Ops.Projects.peer $h _
  | with_reducible exact Ops.Projects.keypair $h _
  | with_reducible exact Ops.Projects.modifyPeer $h _ _
  | with_reducible exact Ops.Projects.guard $h _
  | with_reducible exact Ops.Projects.arm $h _ _ _ _
  | with_reducible exact Ops.Projects.get $h _
  | with_reducible exact Ops.Projects.put $h _
  | with_reducible exact Ops.Projects.append $h _
  | handshake_worker_project_step $rho)

variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem modify_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateProjectsPrefix ρ id (modifyWith g site pid timer delay) (modifyWith t site pid timer delay) := by
  unfold modifyWith
  repeat' first
    | lifetime_effects_project h ρ

theorem traversal_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (traversalWith g pid) (traversalWith t pid) := by
  unfold traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_projects ρ h _ _ _ _
    | lifetime_effects_project h ρ

theorem dataSent_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (dataSentWith g pid) (dataSentWith t pid) := by
  unfold dataSentWith
  repeat' first
    | lifetime_effects_project h ρ

theorem queued_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) (retry : Bool) :
    StateProjectsPrefix ρ id (queuedWith g pid retry) (queuedWith t pid retry) := by
  unfold queuedWith
  repeat' first
    | lifetime_effects_project h ρ

theorem fresh_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (freshWith g pid) (freshWith t pid) := by
  unfold freshWith
  simp only [andPrefix,orPrefix]
  repeat' first
    | with_reducible exact queued_projects ρ h _ _
    | lifetime_effects_project h ρ

end Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffects
