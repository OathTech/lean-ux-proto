import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationRestoreSource

/-! Callback projection for restoration and the following queue operation.
The original no-key source is recovered without changing the order of effects. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects TimerEffects
set_option maxHeartbeats 600000

private theorem loop_projects (ρ : E → Option F) (xs : List α) (initial : β)
    (g : α → β → WGPrefix E (ForInStep β)) (t : α → β → WGPrefix F (ForInStep β))
    (h : ∀ x b, StateProjectsPrefix ρ id (g x b) (t x b)) :
    StateProjectsPrefix ρ id (forIn xs initial g) (forIn xs initial t) := by
  induction xs generalizing initial with
  | nil => intro w a h; rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply StateProjectsPrefix.bind ρ id id (h x initial)
    intro step
    cases step with
    | done b => intro w a h; rfl
    | yield b => exact ih b

theorem noKey_projects (ρ : E → Option F)
    {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)} (h : Ops.Projects ρ g t)
    {restoreG : PeerId → List Packet → WGPrefix E Unit}
    {restoreT : PeerId → List Packet → WGPrefix F Unit}
    {queueG : PeerId → Bool → WGPrefix E Unit}
    {queueT : PeerId → Bool → WGPrefix F Unit}
    (restore : ∀ pid packets, StateProjectsPrefix ρ id (restoreG pid packets) (restoreT pid packets))
    (queue : ∀ pid retry, StateProjectsPrefix ρ id (queueG pid retry) (queueT pid retry))
    (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StateProjectsPrefix ρ id (noKeyWith g restoreG queueG pid packets keypair invalid)
      (noKeyWith t restoreT queueT pid packets keypair invalid) := by
  unfold noKeyWith
  repeat' first
    | exact restore _ _
    | exact queue _ _
    | (maintenance_head ForIn.forIn; apply loop_projects ρ)
    | timer_effects_project h ρ

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
