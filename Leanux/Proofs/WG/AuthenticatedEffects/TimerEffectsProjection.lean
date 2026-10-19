import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsSource

/-! Callback-parametric journal projection through native timer creation and
handshake queueing. Each source executes the exact selected callback once; the
projection includes the retained prefix on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

structure Ops.Projects (ρ : E → Option F) (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F)) : Prop where
  step : ∀ {α} (a : WG.M α), StateProjectsPrefix ρ id (g.step a) (t.step a)
  arm : ∀ pid timer delay caller, StateProjectsPrefix ρ id
    (g.arm pid timer delay caller) (t.arm pid timer delay caller)
  append : ∀ pid, StateProjectsPrefix ρ id (g.append pid) (t.append pid)

macro "timer_effects_project " h:ident rho:ident : tactic => `(tactic| first
  | exact Ops.Projects.step $h _
  | exact Ops.Projects.arm $h _ _ _ _
  | exact Ops.Projects.append $h _
  | handshake_worker_project_step $rho)

variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem modify_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateProjectsPrefix ρ id (modifyWith g site pid timer delay) (modifyWith t site pid timer delay) := by
  unfold modifyWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | timer_effects_project h ρ

theorem derived_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (derivedWith g pid) (derivedWith t pid) := by
  unfold derivedWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_projects ρ h _ _ _ _
    | timer_effects_project h ρ

theorem traversal_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (traversalWith g pid) (traversalWith t pid) := by
  unfold traversalWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_projects ρ h _ _ _ _
    | timer_effects_project h ρ

theorem dataSent_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (dataSentWith g pid) (dataSentWith t pid) := by
  unfold dataSentWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | timer_effects_project h ρ

theorem dataReceived_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (dataReceivedWith g pid) (dataReceivedWith t pid) := by
  unfold dataReceivedWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_projects ρ h _ _ _ _
    | timer_effects_project h ρ

theorem initiated_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (initiatedWith g pid) (initiatedWith t pid) := by
  unfold initiatedWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | timer_effects_project h ρ

theorem queued_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) (retry : Bool) :
    StateProjectsPrefix ρ id (queuedWith g pid retry) (queuedWith t pid retry) := by
  unfold queuedWith
  repeat' first
    | timer_effects_project h ρ

theorem retransmit_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (retransmitWith g pid) (retransmitWith t pid) := by
  unfold retransmitWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_projects ρ h _ _ _ _
    | with_reducible exact queued_projects ρ h _ _
    | timer_effects_project h ρ

theorem expiredNew_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (expiredNewWith g pid) (expiredNewWith t pid) := by
  unfold expiredNewWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact queued_projects ρ h _ _
    | timer_effects_project h ρ

theorem expiredKeepalive_projects (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) (pid : PeerId) :
    StateProjectsPrefix ρ id (expiredKeepaliveWith g kg pid) (expiredKeepaliveWith t kt pid) := by
  unfold expiredKeepaliveWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | exact hk _
    | with_reducible exact modify_projects ρ h _ _ _ _
    | timer_effects_project h ρ

theorem persistent_projects (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) (pid : PeerId) :
    StateProjectsPrefix ρ id (persistentWith g kg pid) (persistentWith t kt pid) := by
  unfold persistentWith
  repeat' first | exact hk _ | timer_effects_project h ρ

theorem timer_projects (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) (pid : PeerId) (timer : PeerTimer) :
    StateProjectsPrefix ρ id (timerWith g kg pid timer) (timerWith t kt pid timer) := by
  cases timer
  · exact retransmit_projects ρ h pid
  · exact expiredKeepalive_projects ρ h kg kt hk pid
  · exact expiredNew_projects ρ h pid
  · exact h.step _
  · exact persistent_projects ρ h kg kt hk pid

end Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
