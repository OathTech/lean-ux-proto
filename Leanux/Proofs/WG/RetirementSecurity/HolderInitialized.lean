import Leanux.Proofs.WG.RetirementSecurity.HolderInitializedSyscall

/-! Normally initialized executions derive exact key reference accounting
from original syscall and scheduler paths. No incoming account, slot-liveness,
receive-ledger or physical-ownership premise is required. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderInitialized
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits

/-- The existing Runner's actual successful World has the complete derived
joint invariant, including the original receive observer's residual ledger. -/
theorem initialized (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) : Inv h w :=
  RunnerInvariant.Normal.executeTraceWith_normal Inv OwnerChecks.Safe safe store
    RxHistory.syscall syscall trace placeholders
    (fun w same=>⟨[],HolderOuter.initial trace.net trace.bare w same⟩) run

/-- At a normal initialized endpoint, every reference count equals the exact
number of actual published-slot, queued-TX-batch and queued-RX-packet holders.
The caller-local ledger is empty; a residual packet holder remains a real debt. -/
theorem account (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    HolderAccount [] w.wg := (initialized trace placeholders run).choose_spec.2.1

/-- Original runner acceptance yields its actual endpoint and exact key
reference ledger. This does not claim that retained packets have drained. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h,runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h) ∧
      HolderAccount [] w.wg := by
  obtain ⟨w,h,_,actual,_,_⟩ := RunnerAccount.accepted trace placeholders run
  exact ⟨w,h,actual,account trace placeholders actual⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderInitialized
