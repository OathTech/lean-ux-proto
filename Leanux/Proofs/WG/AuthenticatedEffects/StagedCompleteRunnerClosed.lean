import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerDeleteSyscall
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterSyscall
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesAdmission

/-! Initialized accounting for the journal actually returned by the native
runner, on normal completion or Stop. Earlier internal prefixes and the
physical correspondence of every stopped cut remain separate obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open TransmitSecurity RetirementSecurity CausalJournal

theorem syscall_closed (call : Syscall) :
    PrefixEnsures Ready CompleteProduct.Safe (Driver.syscallObserved hooks call) (fun _=>Returned) := by
  apply syscall_join call
  · by_cases deletion : call=.wgDelete
    · subst call
      exact PrefixEnsures.consequence DeleteFrames.syscall
        (fun _ _ hi=>⟨hi.1,hi.2.1,hi.2.2.1⟩) (fun _ _ _ hi=>hi)
    · exact PrefixEnsures.consequence (CompleteProduct.Outer.syscall_except_delete call deletion)
        (fun _ _ hi=>hi.1) (fun _ _ _ hi=>hi)
  · exact RetiredPeer.Outer.syscall call

theorem empty_safe : CompleteProduct.Safe [] :=
  ⟨[],.accounted [] [] [] (initialWG false false) (CompleteCarrier.initial false false)⟩

/-- Initialization supplies all native reference and packet companions.
This concludes safety of the reached journal, including a failed execution;
it does not assert safety of arbitrary earlier journal prefixes. -/
theorem reached (trace : Trace) (placeholders : Bool) :
    CompleteProduct.Safe (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 := by
  rw [history_same]
  exact initialized Ready Returned CompleteProduct.Safe empty_safe ready_safe
    ready_prepare ready_close (Driver.syscallObserved hooks) syscall_closed trace placeholders
    (ready_initial trace.net trace.bare)

/-- The actual initialized run supplies one fixed ledger for its reached
history. The account's snapshot retains the limits of `safe_cut`; actual
normal endpoints and general stopped-cut reachability are separate claims. -/
theorem reached_cut (trace : Trace) (placeholders : Bool) :
    ∃ ledger debts locals w, CompleteConsequences.Cut
      (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 ledger debts locals w :=
  CompleteConsequences.safe_cut (reached trace placeholders)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
