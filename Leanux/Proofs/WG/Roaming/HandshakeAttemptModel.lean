import Leanux.Proofs.WG.Roaming.InitiationModel
import Leanux.Proofs.WG.Roaming.ResponseModel
import Leanux.Proofs.WG.Roaming.Model

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeAttempts
open Leanux Leanux.WG

structure Attempt (Cut : Type) where
  cut : Cut
  endpoint : Endpoint
  atSetter : Campaign2.Snapshot

structure Audit (Event : Type) where
  attempts : List Event
  outcome : Campaign2.Outcome Unit

def InitiationFacts (msg : List UInt8) (src : SkbSource)
    (r : Attempt InitiationCallCut) : Prop :=
  InitiationCallFacts msg r.cut ∧ r.endpoint = sourceEndpoint src ∧
    (src.family = 4 ∨ src.family = 6)

def ResponseFacts (msg : List UInt8) (src : SkbSource)
    (r : Attempt ResponseCallCut) : Prop :=
  ResponseCallFacts msg r.cut ∧ r.endpoint = sourceEndpoint src ∧
    (src.family = 4 ∨ src.family = 6)

end Leanux.Proofs.WG.Roaming.HandshakeAttempts
