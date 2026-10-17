import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionModel
import Leanux.Proofs.WG.TimerDiscipline.DataDoneModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

/-- The original response creation/session cut and the traversal it selects. -/
structure ResponseTraversalCall where
  response : Option OutgoingResponseSessionCall
  afterSessionPrefix : Campaign2.Product.Snapshot
  traversal : Option DataDoneTraversalCut

def ResponseTraversalFacts (pid : PeerId) (cut : ResponseTraversalCall) : Prop :=
  (∀ response, cut.response = some response →
    ResponseSessionFacts pid response.session ∧
      responseSessionEnd response.session = cut.afterSessionPrefix) ∧
  cut.traversal.isSome = (cut.response.map (·.session.begun)).getD false ∧
  (∀ hook, cut.traversal = some hook →
    hook.before = cut.afterSessionPrefix ∧ DataDoneTraversalFacts pid hook)


end Leanux.Proofs.WG.TimerDiscipline
