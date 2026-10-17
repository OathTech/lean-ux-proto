import Leanux.Proofs.WG.TimerDiscipline.DataDoneModel
import Leanux.Proofs.WG.Roaming.InitiationCallProductModel
import Leanux.Proofs.WG.Roaming.ResponseCallProductModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

structure ReceiveTraversalCut (α : Type) where
  authentication : α
  traversal : DataDoneTraversalCut

def InitiationReceiveTraversalFacts (msg : List UInt8)
    (cut : ReceiveTraversalCut Roaming.Product.InitiationCallCut) : Prop :=
  Roaming.Product.InitiationCallFacts msg cut.authentication ∧
    DataDoneTraversalFacts cut.authentication.consumed.pid cut.traversal

def ResponseReceiveTraversalFacts (msg : List UInt8)
    (cut : ReceiveTraversalCut Roaming.Product.ResponseCallCut) : Prop :=
  Roaming.Product.ResponseCallFacts msg cut.authentication ∧
    DataDoneTraversalFacts cut.authentication.consumed.input.pid cut.traversal


end Leanux.Proofs.WG.TimerDiscipline
