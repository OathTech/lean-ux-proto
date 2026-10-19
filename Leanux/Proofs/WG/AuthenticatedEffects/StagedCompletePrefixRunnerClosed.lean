import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixRunnerComposition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixOuter
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDeleteSyscall

/-! Every original syscall source is concrete, including guarded deletion.
The initialized theorem covers every logical journal prefix on normal return
or Stop. A prefix's existential account is not itself a native reached cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open TransmitSecurity RetirementSecurity CausalJournal CompleteRunner

theorem syscall (call : Syscall) :
    Ensures Ready CompleteProduct.Safe (Driver.syscallObserved hooks call) (fun _=>Returned) := by
  apply syscall_join call
  by_cases deletion : call=.wgDelete
  · subst call
    exact Delete.syscall.consequence (fun _ _ before=>⟨before.1,before.2.1,before.2.2.1⟩)
      (fun _ _ _ after=>after)
  · exact (Product.Outer.syscall_except_delete call deletion).consequence
      (fun _ _ before=>before.1) (fun _ _ _ after=>after)

/-- All journal prefixes of the actual initialized execution retain their
own paired accounting certificate. No callback or incoming carrier is assumed;
native correspondence between receipts is a separate obligation. -/
theorem reached (trace : Trace) (placeholders : Bool) :
    All CompleteProduct.Safe (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 :=
  initialized_from_syscalls syscall trace placeholders

theorem prefix_cut (trace : Trace) (placeholders : Bool)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2=earlier++suffix) :
    ∃ ledger debts locals w, CompleteConsequences.Cut earlier ledger debts locals w :=
  CompleteConsequences.safe_cut ((reached trace placeholders).at_prefix position)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner
