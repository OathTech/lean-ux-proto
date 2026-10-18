import Leanux.Proofs.WG.Index.InitializedFundingFrames
import Leanux.Proofs.WG.Index.FundedBaseSource
import Leanux.Proofs.WG.Index.InitializedBoundsClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.InitializedFunding
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem runner_live (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (w : World) (history : List RxHistory.Event)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) [] =
      (.ok (json,w),history)) :
    LivePeerCredit (Campaign2.snapshot w.wg w.ambient) := by
  obtain ⟨ledger,certificate,entry⟩ := RunnerAccount.normal trace placeholders run
  exact holder_entry_live ledger [] history w entry

end Leanux.Proofs.WG.Index.InitializedFunding
