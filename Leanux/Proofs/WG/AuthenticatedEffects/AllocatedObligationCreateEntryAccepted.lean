import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryFrames

/-! Accepted and EPIPE returns perform only their actual source guards. The
already transferred queue ownership and exact incoming ledger/debts survive. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal

/-- A successful or EPIPE admission returns without a cleanup obligation:
the original tail is total and preserves the same full entry and history. -/
theorem accepted_tail (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int)
    (accepted : ret = 0 ∨ ret = -WG.EPIPE)
    (before : StagedEntry.Inv history ledger debts locals w.wg) :
    ∃ v, runPrefix (Admission.tail Admission.actualOps free pid items first ret) w history =
      (.ok ((),v),history) ∧ StagedEntry.Inv history ledger debts locals v.wg := by
  rw [tail_factor,beforeFree_release_factor]
  rcases accepted with zero | pipe
  · subst ret
    obtain ⟨v,guard,final⟩ := guard_entry .createDataOk true before
    refine ⟨v,?_,final⟩
    simp only [runPrefix_bind,show ((0 : Int) == 0) = true from rfl,guard,
      ite_true,runPrefix_pure,Bool.false_eq_true,ite_false]
  · subst ret
    obtain ⟨u,guard,atPipe⟩ := guard_entry .createDataOk false before
    obtain ⟨v,checked,final⟩ := guard_entry .createDataOkEpipe true atPipe
    refine ⟨v,?_,final⟩
    simp only [runPrefix_bind,show (-WG.EPIPE == (0 : Int)) = false from rfl,guard,
      Bool.false_eq_true,ite_false,show (-WG.EPIPE == -WG.EPIPE) = true from rfl,
      checked,ite_true,runPrefix_pure]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
