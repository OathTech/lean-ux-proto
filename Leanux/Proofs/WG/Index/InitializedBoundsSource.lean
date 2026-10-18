import Leanux.Proofs.WG.Index.InitializedBoundsFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.InitializedBounds
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

/-! Source: the landed paired account runner supplies the same actual normal
World, source-selected ledger and complete incoming record execution. -/
theorem runner_normal (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (w : World) (history : List RxHistory.Event)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) [] =
      (.ok (json,w),history)) :
    EndpointSafe (Campaign2.snapshot w.wg w.ambient) := by
  obtain ⟨ledger,certificate,entry⟩ := RunnerAccount.normal trace placeholders run
  exact holder_entry_projection ledger [] history w entry

theorem runner_accepted (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (run : Runner.executeTrace trace placeholders = .ok json) :
    ∃ w history, runPrefixOuter (RunnerAccount.observed trace placeholders) [] =
      (.ok (json,w),history) ∧ EndpointSafe (Campaign2.snapshot w.wg w.ambient) := by
  obtain ⟨w,history,ledger,actual,certificate,entry⟩ :=
    RunnerAccount.accepted trace placeholders run
  exact ⟨w,history,actual,holder_entry_projection ledger [] history w entry⟩


end Leanux.Proofs.WG.Index.InitializedBounds
