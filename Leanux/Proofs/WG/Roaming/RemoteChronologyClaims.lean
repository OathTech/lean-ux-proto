import Leanux.Proofs.WG.Roaming.RemoteChronologyOriginSource
import Leanux.Proofs.WG.Roaming.RemoteChronologyRunnerSource
import Leanux.Proofs.WG.Roaming.RemoteProvenanceClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology
open Lean Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged

/-- Every surviving initialized endpoint is explained by the actual latest
setter for that store location, with no later setter or allocation reset. -/
theorem final_latest_origins (trace : Runner.Trace) (placeholders : Bool)
    (json : Json) (final : Campaign2.Snapshot)
    (completed : RemoteProvenance.outcome trace placeholders = .ok (json,final)) :
    ∀ pid remote, remoteMap final pid = some remote →
      ∃ q : LatestOrigin, q.Valid trace placeholders pid remote ∧ q.origin.Facts pid remote := by
  cases run : runPrefixOuter (RemoteDriver.Runner.observed trace placeholders) [] with
  | mk result h =>
    cases result with
    | error stop =>
      simp only [RemoteProvenance.outcome,run,Except.map] at completed
      cases completed
    | ok result =>
      obtain ⟨j,w⟩ := result
      simp only [RemoteProvenance.outcome,run,Except.map,Except.ok.injEq,Prod.mk.injEq] at completed
      obtain ⟨rfl,rfl⟩ := completed
      have good := Driver.Runner.normal trace placeholders j w h run
      have actual : h = RemoteDriver.Runner.history trace placeholders := by
        simp [RemoteDriver.Runner.history,run]
      exact latest_of_order trace placeholders h (destinationAt w.wg) actual good.2 good.1

end Leanux.Proofs.WG.Roaming.RemoteChronology
