import Leanux.Proofs.WG.Index.InitializedFundingSource
import Leanux.Proofs.WG.Index.FundedBaseSource
import Leanux.Proofs.WG.Index.InitializedBoundsClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.InitializedFunding
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem inspection_live (trace : Runner.Trace) (placeholders : Bool) :
    match InitializedBounds.inspection trace placeholders with
    | .error _ => True
    | .ok (_,final) => LivePeerCredit final := by
  cases run : runPrefixOuter (RunnerAccount.observed trace placeholders) [] with
  | mk outcome history =>
    cases outcome with
    | error stop => simp only [InitializedBounds.inspection,run,Except.map]
    | ok out =>
      obtain ⟨json,w⟩ := out
      simpa only [InitializedBounds.inspection,run,Except.map] using
        runner_live trace placeholders json w history run

theorem accepted_live (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (accepted : Runner.executeTrace trace placeholders = .ok json) :
    ∃ final, InitializedBounds.inspection trace placeholders = .ok (json,final) ∧
      LivePeerCredit final := by
  obtain ⟨w,history,ledger,run,certificate,entry⟩ :=
    RunnerAccount.accepted trace placeholders accepted
  exact ⟨Campaign2.snapshot w.wg w.ambient,
    by simp only [InitializedBounds.inspection,run,Except.map],
    holder_entry_live ledger [] history w entry⟩

end Leanux.Proofs.WG.Index.InitializedFunding
