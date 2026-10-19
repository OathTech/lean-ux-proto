import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsSource

/-! Exact source projection for packet-side timer and queued-handshake effects.
The original guards and retained Stop prefixes are preserved. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.PacketEffects
open Leanux Leanux.WG Leanux.Proofs.Logged TimerEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

private theorem project_loop (ρ : E → Option F) (xs : List α) (initial : β)
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

theorem freshSend_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (freshSendWith g pid) (freshSendWith t pid) := by
  unfold freshSendWith
  repeat' first | with_reducible exact queued_projects ρ h _ _ | timer_effects_project h ρ

theorem freshReceive_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (freshReceiveWith g pid) (freshReceiveWith t pid) := by
  unfold freshReceiveWith
  repeat' first | with_reducible exact queued_projects ρ h _ _ | timer_effects_project h ρ

theorem noKey_projects (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StateProjectsPrefix ρ id (noKeyWith g pid packets keypair invalid) (noKeyWith t pid packets keypair invalid) := by
  unfold noKeyWith
  repeat' first
    | with_reducible exact queued_projects ρ h _ _
    | (maintenance_head ForIn.forIn; apply project_loop ρ)
    | timer_effects_project h ρ

theorem prepare_projects (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (pid : PeerId) (pkt : RxPacket) :
    StateProjectsPrefix ρ id (prepareWith g pid pkt) (prepareWith t pid pkt) := by
  unfold prepareWith
  repeat' first
    | with_reducible exact freshReceive_projects ρ h _
    | with_reducible exact traversal_projects ρ h _
    | with_reducible exact dataReceived_projects ρ h _
    | timer_effects_project h ρ

end Leanux.Proofs.WG.AuthenticatedEffects.PacketEffects
