import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCryptPollPointCoverage
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointInitialized

/-! Actual committed encryption iteration uses the closed polling source.
All other worker relations are retained, rather than replaced by boundaries. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CryptPoll.Composition
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def iterationPoints (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  fun token w h u middle => match token with
  | .poll => Points.RootPoints w h u middle
  | token => other token w h u middle

noncomputable def poll
    {native inside : Iteration.Points.ChildPoints} {Good : History → World → Prop}
    (accept : ∀ledger h w,CompleteCarrier.Accounted h ledger [] [] w.wg → Good h w) :
    Iteration.Points.ChildSourceContract (iterationPoints native) (iterationPoints inside) Good .poll where
  remainder := Points.remainder
  continuation := fun _ _ _ _ point => Points.remainder_run point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before.1
    exact accept ledger middle u ((Points.source_accounted accounted point).1)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CryptPoll.Composition
