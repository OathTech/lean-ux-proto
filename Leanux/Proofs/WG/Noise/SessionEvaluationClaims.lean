import Leanux.Proofs.WG.Noise.SessionEvaluationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.SessionEvaluation
open Leanux Leanux.WG

/-- All concrete entry states and allocation modes retain their exact original
outcomes under the finite evaluator, including missing-input and invariant Stops. -/
theorem original_session_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (beginSession pid) (evaluate pid) := by
  rw [evaluate_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Noise.SessionEvaluation
