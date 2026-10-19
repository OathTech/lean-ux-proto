import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects

/-! Projection-specific history frames for native timer/work effects. These
preserve lexical scope histories while the actual effect receipts are appended. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

structure Ops.Frames (ρ : E → Option F) (g : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (a : WG.M α), StateHistoryFrame ρ (g.step a)
  arm : ∀ pid timer delay caller, StateHistoryFrame ρ (g.arm pid timer delay caller)
  append : ∀ pid, StateHistoryFrame ρ (g.append pid)

private theorem frame_pure (ρ : E → Option F) (x : α) : StateHistoryFrame ρ (pure x : WGPrefix E α) := by
  intro w a h
  rfl
private theorem frame_choice (ρ : E → Option F) (p : Prop) [Decidable p] (g t : WGPrefix E α)
    (hg : StateHistoryFrame ρ g) (ht : StateHistoryFrame ρ t) :
    StateHistoryFrame ρ (if p then g else t) := by split <;> assumption

theorem frame_loop (ρ : E → Option F) (xs : List α) (initial : β)
    (g : α → β → WGPrefix E (ForInStep β))
    (h : ∀ x b, StateHistoryFrame ρ (g x b)) : StateHistoryFrame ρ (forIn xs initial g) := by
  induction xs generalizing initial with
  | nil => intro w a h; rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StateHistoryFrame.bind (h x initial)
    intro step
    cases step with
    | done b => exact frame_pure ρ _
    | yield b => exact ih b

macro "timer_effects_frame_step " rho:ident : tactic => `(tactic| first
  | with_reducible exact frame_pure $rho _
  | with_reducible apply frame_loop $rho
  | with_reducible apply StateHistoryFrame.bind
  | with_reducible apply frame_choice $rho
  | contradiction
  | split
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

macro "timer_effects_frame " h:ident rho:ident : tactic => `(tactic| first
  | with_reducible exact Ops.Frames.step $h _
  | with_reducible exact Ops.Frames.arm $h _ _ _ _
  | with_reducible exact Ops.Frames.append $h _
  | timer_effects_frame_step $rho)

variable {g : Ops (WGPrefix E)}

theorem modify_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateHistoryFrame ρ (modifyWith g site pid timer delay) := by
  unfold modifyWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | timer_effects_frame h ρ

theorem derived_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (derivedWith g pid) := by
  unfold derivedWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_frame ρ h _ _ _ _
    | timer_effects_frame h ρ

theorem traversal_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (traversalWith g pid) := by
  unfold traversalWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_frame ρ h _ _ _ _
    | timer_effects_frame h ρ

theorem dataSent_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (dataSentWith g pid) := by
  unfold dataSentWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | timer_effects_frame h ρ

theorem dataReceived_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (dataReceivedWith g pid) := by
  unfold dataReceivedWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_frame ρ h _ _ _ _
    | timer_effects_frame h ρ

theorem initiated_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (initiatedWith g pid) := by
  unfold initiatedWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | timer_effects_frame h ρ

theorem queued_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) (retry : Bool) :
    StateHistoryFrame ρ (queuedWith g pid retry) := by
  unfold queuedWith
  repeat' first
    | timer_effects_frame h ρ

theorem retransmit_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (retransmitWith g pid) := by
  unfold retransmitWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_frame ρ h _ _ _ _
    | with_reducible exact queued_frame ρ h _ _
    | timer_effects_frame h ρ

theorem expiredNew_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (expiredNewWith g pid) := by
  unfold expiredNewWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact queued_frame ρ h _ _
    | timer_effects_frame h ρ

theorem expiredKeepalive_frame (ρ : E → Option F) (h : Ops.Frames ρ g)
    (keepalive : PeerId → WGPrefix E Unit) (hk : ∀ pid, StateHistoryFrame ρ (keepalive pid))
    (pid : PeerId) : StateHistoryFrame ρ (expiredKeepaliveWith g keepalive pid) := by
  unfold expiredKeepaliveWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact hk _
    | with_reducible exact modify_frame ρ h _ _ _ _
    | timer_effects_frame h ρ

theorem persistent_frame (ρ : E → Option F) (h : Ops.Frames ρ g)
    (keepalive : PeerId → WGPrefix E Unit) (hk : ∀ pid, StateHistoryFrame ρ (keepalive pid))
    (pid : PeerId) : StateHistoryFrame ρ (persistentWith g keepalive pid) := by
  unfold persistentWith
  repeat' first
    | with_reducible exact hk _
    | timer_effects_frame h ρ

theorem timer_frame (ρ : E → Option F) (h : Ops.Frames ρ g)
    (keepalive : PeerId → WGPrefix E Unit) (hk : ∀ pid, StateHistoryFrame ρ (keepalive pid))
    (pid : PeerId) (timer : PeerTimer) : StateHistoryFrame ρ (timerWith g keepalive pid timer) := by
  cases timer
  · exact retransmit_frame ρ h pid
  · exact expiredKeepalive_frame ρ h keepalive hk pid
  · exact expiredNew_frame ρ h pid
  · exact h.step _
  · exact persistent_frame ρ h keepalive hk pid

end Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
