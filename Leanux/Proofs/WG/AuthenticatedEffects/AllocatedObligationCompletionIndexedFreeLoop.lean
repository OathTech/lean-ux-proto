import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionLocalDebts

/-! The actual ordinary cleanup loop returns the idle empty-debt boundary.
Each step is total from native selected-cell backing, and only the original
reason-free free is performed; no extra terminal is introduced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts HandshakeSecurity.StagedDisposal

/-- Every local debt is discharged by its own native free. On return the
canonical terminal ledger is unchanged and the original empty debt list is
restored, with no native-free success assumption supplied. -/
theorem indexed_freeLoop_total (remaining : List SkbId)
    (before : Owned context (.freeing remaining) history ledger debts w)
    (localDebts : LocalDebts context remaining debts) :
    ∃ v suffix,
      runPrefix (freeLoop (TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal) remaining) w history = (.ok ((),v),history ++ suffix) ∧
      Owned context (.freeing []) (history ++ suffix) ledger [] v := by
  induction remaining generalizing history debts w with
  | nil =>
    have empty := localDebts.finished
    subst debts
    exact ⟨w,[],by simp [freeLoop,runPrefix_pure],by simpa only [List.append_nil] using before⟩
  | cons skb rest ih =>
    obtain ⟨u,first,generation,performed,atCut,kept⟩ := indexed_free_local before localDebts
    obtain ⟨v,tail,finished,after⟩ := ih atCut kept
    refine ⟨v,first ++ tail,?_,?_⟩
    · change runPrefix (FirstTerminal.cleanupFree skb >>= fun _ =>
        freeLoop (TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
          CausalJournal.Event.stagedDisposal) rest) w history = _
      rw [runPrefix_bind,performed]
      simpa only [List.append_assoc] using finished
    · simpa only [List.append_assoc] using after

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
