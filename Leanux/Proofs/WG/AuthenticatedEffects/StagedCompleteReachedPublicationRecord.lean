import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPublicationPath

/-! The existing published event is tied to the preceding original head
write and its returned World. It is not upgraded from IDs into a snapshot
without that source execution witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation HandshakeSecurity.StagedDisposal

def publicationWrite (pid : PeerId) (first : SkbId) (state : PacketState) : PrefixM CausalJournal.Event Unit := do
  if !((← Admission.actualOps.access (getPeerMixed pid)).txQueue.all.any (·.head? == some first)) then
    Admission.actualOps.step (invariant "an item for the tx worker that is not on its peer's tx_queue")
  Admission.actualOps.access (setTxSkbPrefix first fun p => {p with state})

theorem publication_write_factor (pid : PeerId) (first : SkbId) (state : PacketState) :
    publicationMark pid first state = (do
      publicationWrite pid first state
      Admission.actualOps.event (.published pid first state)) := by
  simp only [publicationMark,publicationWrite,bind_assoc,TxDisposition.bind_ite]

theorem publication_event_run (pid : PeerId) (first : SkbId) (state : PacketState)
    (w : World) (history : List CausalJournal.Event) :
    runPrefix (Admission.actualOps.event (.published pid first state)) w history =
      (.ok ((),w),history ++ [CausalJournal.txEvent (.published pid first state)]) := by
  simpa only [Admission.actualOps,TxSource.observed,TxSource.Ops.focus,TxSource.native,List.map_cons,List.map_nil] using
    focusPrefix_suffix CausalJournal.txEvent CausalJournal.txEvent?
      (emitPrefix (.published pid first state)) w history (.ok ((),w)) [.published pid first state] rfl

/-- The recorded publication position immediately follows the actual head
write at the same World; no later scheduler or repayment return is needed. -/
theorem publication_recorded
    (performed : runPrefix (publicationMark pid first state) w history = (.ok ((),v),last)) :
    ∃ writtenHistory,
      runPrefix (publicationWrite pid first state) w history = (.ok ((),v),writtenHistory) ∧
      last = writtenHistory ++ [CausalJournal.txEvent (.published pid first state)] := by
  rw [publication_write_factor,runPrefix_bind] at performed
  cases written : runPrefix (publicationWrite pid first state) w history with
  | mk outcome writtenHistory =>
    rw [written] at performed
    cases outcome with
    | error reason => cases performed
    | ok out =>
      obtain ⟨ignored,u⟩ := out
      cases ignored
      dsimp only at performed
      rw [publication_event_run] at performed
      simp only [Prod.mk.injEq,Except.ok.injEq] at performed
      obtain ⟨⟨_,rfl⟩,rfl⟩ := performed
      exact ⟨writtenHistory,rfl,rfl⟩

theorem PublishedPath.recorded
    (path : PublishedPath ledger debts locals items state w history first pid v last) :
    ∃ u middle writtenHistory,
      runPrefix (Publication.borrow items) w history = (.ok ((first,pid),u),middle) ∧
      runPrefix (publicationWrite pid first state) u middle = (.ok ((),v),writtenHistory) ∧
      last = writtenHistory ++ [CausalJournal.txEvent (.published pid first state)] ∧
      Accounted last ledger debts locals v.wg := by
  cases path with
  | marked u middle initial borrowed beforeMark marked afterMark =>
    obtain ⟨writtenHistory,written,event⟩ := publication_recorded marked
    exact ⟨u,middle,writtenHistory,borrowed,written,event,afterMark⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
