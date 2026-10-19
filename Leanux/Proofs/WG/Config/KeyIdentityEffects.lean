import Leanux.Proofs.WG.Config.KeyIdentityModel
import Leanux.Proofs.WG.Config.KeyObservationFrames

/-! Identity and clamped-key consequences of the existing stage effect. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise TimerDiscipline
namespace KeyStage
theorem effect_identity (attrs : DeviceAttrs) (before after : Device)
    (effect : Effect attrs before after) : IdentityEffect attrs before after.staticIdentity := by
  cases effect with
  | absent none => simp only [IdentityEffect,none]
  | unchanged key some same => simp only [IdentityEffect,some,same,ite_true]
  | changed key some different baseline after generated observations installed =>
    simp only [IdentityEffect,some,different,ite_false]
    refine ⟨baseline,generated,?_⟩
    have same:=observedKeyPeerRun_header _ _ _ _ _ installed
    exact congrArg (fun header : SendConfiguration=>header.2.2.2.2.1) same

theorem identityEffect_private (attrs : DeviceAttrs) (before : Device) (identity : StaticIdentity)
    (effect : IdentityEffect attrs before identity) (key : Key) (given : attrs.privateKey=some key) :
    identity.staticPrivate=if before.staticIdentity.staticPrivate=key then key else clamp key := by
  simp only [IdentityEffect,given] at effect
  split at effect
  · rename_i same
    rw [effect]
    simp only [same,ite_true]
  · rename_i different
    obtain ⟨baseline,_,same⟩:=effect
    rw [same]
    simp only [different,ite_false,identityAfter]

end KeyStage
end Leanux.Proofs.WG.Config

