import Leanux.Proofs.WG.Index.ReachedSyscallSource
import Leanux.Proofs.WG.Index.ReachedInitializedModel
import Leanux.Proofs.WG.Index.ReachedRunnerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedTraffic
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem initialized (trace : Runner.Trace) (placeholders : Bool) (json : Lean.Json) (w : World)
    (history : List RxHistory.Event)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (json,w),history)) :
    Reached.AnyEntry history w :=
  Reached.runner_core_of_syscalls (syscall) trace placeholders json w history run

end Leanux.Proofs.WG.Index.ReachedTraffic

namespace Leanux.Proofs.WG.Index.ReachedInitialized
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

def inspection (trace : Runner.Trace) (placeholders : Bool) : Inspection :=
  (runPrefixOuter (RunnerAccount.observed trace placeholders) []).1.map
    (fun (json,w)=>(json,Campaign2.Product.snapshot w))

/-- The residual source-selected account of this exact initialized execution.
It does not assert that the remaining ledger or work set is empty. -/
def ActualAccount (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ w history ledger,
    runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (json,w),history) ∧
    Campaign2.Product.snapshot w=final ∧
    (RunnerAccount.rule trace placeholders).relation [] [] (json,w) history ledger ∧
    HolderEntry.Inv ledger [] history w

end Leanux.Proofs.WG.Index.ReachedInitialized
