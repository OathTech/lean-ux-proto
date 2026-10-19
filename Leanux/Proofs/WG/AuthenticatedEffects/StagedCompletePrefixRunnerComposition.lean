import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixRunnerFrames

/-! Whole initialized prefix composition reuses the original operation loop,
its preparation and its actual return guard. Concrete syscall source contracts
are explicit until discharged; this is not a native internal-cut relation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open TransmitSecurity RetirementSecurity CausalJournal CompleteRunner

theorem syscall_join (call : Syscall)
    (prefixes : Ensures Ready CompleteProduct.Safe
      (Driver.syscallObserved hooks call) (fun _=>CompleteProduct.Carrier)) :
    Ensures Ready CompleteProduct.Safe (Driver.syscallObserved hooks call) (fun _=>Returned) :=
  prefixes.join (syscall_closed call) (fun _ _ before=>before)

theorem initialized_from_syscalls
    (calls : ∀ call, Ensures Ready CompleteProduct.Safe
      (Driver.syscallObserved hooks call) (fun _=>Returned))
    (trace : Trace) (placeholders : Bool) :
    All CompleteProduct.Safe (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 := by
  rw [history_same]
  exact CompleteRunner.initialized Entry Exit (All CompleteProduct.Safe) (All.nil empty_safe)
    safe prepare close (Driver.syscallObserved hooks) calls trace placeholders
    (initial trace.net trace.bare)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner
