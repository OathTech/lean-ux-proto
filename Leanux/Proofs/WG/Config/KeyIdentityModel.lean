import Leanux.Proofs.WG.Config.KeyStageModel

/-! Identity installed by the actual key stage, retaining its collision baseline. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise
namespace KeyStage
def IdentityEffect (attrs : DeviceAttrs) (before : Device) (identity : StaticIdentity) : Prop :=
  match attrs.privateKey with
  | none => identity=before.staticIdentity
  | some key => if before.staticIdentity.staticPrivate=key then identity=before.staticIdentity
    else ∃ baseline,GeneratedEffect before key baseline ∧ identity=identityAfter key baseline.staticIdentity


end KeyStage
end Leanux.Proofs.WG.Config

