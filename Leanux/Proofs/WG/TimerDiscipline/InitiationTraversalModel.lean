import Leanux.Proofs.WG.TimerDiscipline.DataDoneModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- The actual MAC-added initiation and optional traversal invocation. -/
structure InitiationTraversalCall where
  message : Option (List UInt8)
  traversal : Option DataDoneTraversalCut

def InitiationTraversalFacts (pid : PeerId) (cut : InitiationTraversalCall) : Prop :=
  cut.traversal.isSome = cut.message.isSome ∧
  ∀ hook, cut.traversal = some hook → DataDoneTraversalFacts pid hook

end Leanux.Proofs.WG.TimerDiscipline
