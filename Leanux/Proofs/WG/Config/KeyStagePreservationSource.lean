import Leanux.Proofs.WG.Config.KeyStageSource
import Leanux.Proofs.WG.Index.ConfigurationKeyRulesSource

/-! Generic rules extracted from the owned final-header proof; original program factors and key-installation rule are unchanged. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.KeyStage
open Leanux Leanux.WG Noise TimerDiscipline
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem collision_preserves (P : WGWorld → Prop)
    (c : Index.ConfigurationKeyRules.Contracts P) (key : Key) :
    Preserves P (keyCollisionSource key) := by
  unfold keyCollisionSource keyCollisionSourceWith
  apply preserves_bind ((generatePublic_sameWGWorld key).wp P)
  rintro ⟨pub,ok⟩
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevGenPublic ok) P)
  intro generated
  cases generated with
  | false => exact (SameView.pure (id : WGWorld→WGWorld) ()).wp P
  | true =>
    cases pub with
    | none => exact hoare_liftAmbient (AmbientM.invariant _) P
    | some pub => exact c.conflict pub

theorem stage_preserves (P : WGWorld → Prop)
    (c : Index.ConfigurationKeyRules.Contracts P) (attrs : DeviceAttrs) :
    Preserves P (RequestOrder.keyStage attrs) := by
  rw [stage_factor]
  unfold WG.andM
  repeat' first
    | (rx_retention_head getDev; exact c.read)
    | (rx_retention_head keyCollisionSource; exact collision_preserves P c _)
    | (rx_retention_head keyInstallSource
       rw [install_factor]
       exact Index.ConfigurationKeyRules.keyFinish P c _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | rx_retention_step
end Leanux.Proofs.WG.Config.KeyStage
