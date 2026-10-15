import Leanux.Proofs.WG.TimerDiscipline.DataDoneModel
import Leanux.Proofs.WG.Roaming.InitiationModel
import Leanux.Proofs.WG.Roaming.ResponseModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Roaming

structure ReceiveTraversalCut (α : Type) where
  authentication : α
  traversal : DataDoneTraversalCut

def InitiationReceiveTraversalFacts (msg : List UInt8)
    (cut : ReceiveTraversalCut InitiationCallCut) : Prop :=
  InitiationCallFacts msg cut.authentication ∧
    DataDoneTraversalFacts cut.authentication.consumed.pid cut.traversal

def ResponseReceiveTraversalFacts (msg : List UInt8)
    (cut : ReceiveTraversalCut ResponseCallCut) : Prop :=
  ResponseCallFacts msg cut.authentication ∧
    DataDoneTraversalFacts cut.authentication.consumed.input.pid cut.traversal

end Leanux.Proofs.WG.TimerDiscipline
