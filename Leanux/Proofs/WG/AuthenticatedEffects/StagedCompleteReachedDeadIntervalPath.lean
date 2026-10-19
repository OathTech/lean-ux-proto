import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadIntervalStep

/-! Paths are the original ordered free iterations, not arbitrary program
factors. Each boundary retains native ownership of precisely the remaining
selected suffix and all earlier terminal outcomes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeadIntervals
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation

theorem Path.entry
    (path : Path reason pid debts locals n items w history ledger v last after) :
    Accounted history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg ∧
      PendingBatch history ledger items := by
  cases path with
  | nil before pending => exact ⟨before,pending⟩
  | cons first _ => exact ⟨first.entry,first.pending⟩

theorem Path.result
    (path : Path reason pid debts locals n items w history ledger v last after) :
    Staged.Obligations.Step ledger after ∧
      Accounted last after debts (⟨.selected,pid,items.drop n⟩ :: locals) v.wg ∧
      PendingBatch last after (items.drop n) := by
  induction path with
  | nil before pending => exact ⟨.refl _,before,pending⟩
  | cons first rest ih =>
    exact ⟨first.result.1.trans ih.1,by simpa only [List.drop_succ_cons] using ih.2.1,
      by simpa only [List.drop_succ_cons] using ih.2.2⟩

theorem Path.run
    (path : Path reason pid debts locals n items w history ledger v last after) :
    runPrefix (loop reason (items.take n)) w history = (.ok ((),v),last) := by
  induction path with
  | nil => simp [loop,runPrefix_pure]
  | cons first rest ih =>
    rw [List.take_succ_cons,loop_cons,runPrefix_bind,first.run]
    exact ih

theorem Path.bound
    (path : Path reason pid debts locals n items w history ledger v last after) : n ≤ items.length := by
  induction path with
  | nil => omega
  | cons first rest ih => simp only [List.length_cons]; omega

theorem Path.append
    (path : Path reason pid debts locals n items w history ledger v last after) :
    ∃ suffix, last = history ++ suffix := by
  induction path with
  | nil => exact ⟨[],by simp⟩
  | cons first rest ih =>
    obtain ⟨a,firstEq⟩ := first.append
    obtain ⟨b,restEq⟩ := ih
    exact ⟨a ++ b,by rw [restEq,firstEq,List.append_assoc]⟩

theorem Path.dropped
    (path : Path reason pid debts locals n items w history ledger v last after) :
    AllDropped last after reason (items.take n) := by
  induction path with
  | nil => intro id member; cases member
  | cons first rest ih =>
    obtain ⟨suffix,grown⟩ := rest.append
    intro id member
    simp only [List.take_succ_cons,List.mem_cons] at member
    rcases member with rfl | later
    · simpa only [←grown] using first.result.2.2.2.transport suffix rest.result.1
    · exact ih id later

theorem total (reason : Terminal.Reason) (items : List SkbId)
    (before : Accounted history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ v last after, Path reason pid debts locals items.length items w history ledger v last after := by
  induction items generalizing w history ledger with
  | nil => exact ⟨w,history,ledger,.nil before pending⟩
  | cons id items ih =>
    obtain ⟨u,middle,next,first⟩ := iteration_total reason id before pending
    obtain ⟨v,last,after,rest⟩ := ih first.result.2.1 first.result.2.2.1
    exact ⟨v,last,after,.cons first rest⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeadIntervals
