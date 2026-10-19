import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteReleaseFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPublicationRepayment
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryFront

/-! Actual publication preserves terminal completeness because its own borrow
funds a nonfinal repayment. The proof follows that source cut even on Stop;
a generic birth-free or native endpoint frame would not imply this result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete HandshakeSecurity.StagedDisposal

/-- Every event produced by the actual TX-access focus is terminal-quiet. -/
theorem focused_complete (body : TxDisposition.Obs α) (w : World)
    (before : Complete history ledger) :
    Complete (runPrefix (QueueHandoff.focused body) w history).2 ledger := by
  change Complete (history ++ _) ledger
  apply before.append_quiet
  intro event member
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  intro position
  rfl

theorem focused_history (body : TxDisposition.Obs α) :
    Driver.ProductHistorySafe (fun h => Complete h ledger) (QueueHandoff.focused body) := by
  intro w h before
  obtain ⟨suffix,extended⟩ := Appends.focus CausalJournal.txEvent CausalJournal.txEvent? body w h
  have kept := focused_complete body w before
  refine ⟨suffix,extended,kept,?_⟩
  cases result : (runPrefix (QueueHandoff.focused body) w h).1 with
  | error stop => trivial
  | ok out => exact kept

theorem borrow_history (items : List SkbId) :
    Driver.ProductHistorySafe (fun h => Complete h ledger) (Publication.borrow items) := by
  unfold Publication.borrow Admission.actualOps
  simp only [TxSource.observed,TxSource.Ops.focus]
  cases items.head? with
  | none => exact focused_history _
  | some first =>
    repeat' first
      | (driver_history_head focusPrefix; exact focused_history _)
      | driver_product_history_step

theorem middle_history (pid : PeerId) (first : SkbId) (state : PacketState) :
    Driver.ProductHistorySafe (fun h => Complete h ledger) (Publication.middle pid first state) := by
  unfold Publication.middle Admission.actualOps
  simp only [TxSource.observed,TxSource.Ops.focus]
  repeat' first
    | (driver_history_head focusPrefix; exact focused_history _)
    | driver_product_history_step

/-- The actual reached publication repayment has a none-valued receipt,
proved from its source borrow and middle; no terminal event is discarded. -/
theorem publication_complete (items : List SkbId) (state : PacketState) (w : World)
    (before : Complete history ledger) :
    Complete (runPrefix (TxSource.publish Admission.actualOps items state) w history).2 ledger := by
  rw [Publication.factor,runPrefix_bind]
  obtain ⟨_,_,borrowComplete,_⟩ := borrow_history items w history before
  cases acquired : runPrefix (Publication.borrow items) w history with
  | mk outcome borrowHistory =>
    rw [acquired] at borrowComplete
    cases outcome with
    | error stop => exact borrowComplete
    | ok out =>
      obtain ⟨⟨first,pid⟩,u⟩ := out
      simp only [runPrefix_bind]
      obtain ⟨_,_,middleComplete,_⟩ := middle_history pid first state u borrowHistory borrowComplete
      cases published : runPrefix (Publication.middle pid first state) u borrowHistory with
      | mk result publishedHistory =>
        rw [published] at middleComplete
        cases result with
        | error stop => exact middleComplete
        | ok out =>
          obtain ⟨ignored,v⟩ := out
          cases ignored
          have funded := Publication.observed_middle_funded pid first state
            (Publication.observed_borrow_funded items acquired) published
          obtain ⟨g,ambient,cutHistory,cut,returned,_,_⟩ :=
            Publication.repayment_nonfinal pid funded publishedHistory
          simp only []
          rw [returned]
          have cutComplete := StagedTerminalComplete.Source.cut_complete (some pid) v.wg v.ambient middleComplete
          rw [cut] at cutComplete
          apply cutComplete.append_quiet
          intro event member
          cases List.mem_singleton.mp member
          exact release_none_quiet rfl

theorem publication_history (items : List SkbId) (state : PacketState) :
    Driver.ProductHistorySafe (fun h => Complete h ledger)
      (TxSource.publish Admission.actualOps items state) := by
  intro w h before
  obtain ⟨suffix,extended⟩ := Admission.publication_appends items state w h
  have kept := publication_complete items state w before
  refine ⟨suffix,extended,kept,?_⟩
  cases result : (runPrefix (TxSource.publish Admission.actualOps items state) w h).1 with
  | error stop => trivial
  | ok out => exact kept

/-- Actual creation admission preserves all prior receipt cardinalities.
The only nested release is source-proved nonfinal; later refusal cleanup is
outside this prefix and requires its own exact settlements. -/
theorem admission_history (pid : PeerId) (items : List SkbId) :
    Driver.ProductHistorySafe (fun h => Complete h ledger) (Admission.actual pid items) := by
  unfold Admission.actual Admission.front
  repeat' first
    | (driver_history_head TxSource.publish; exact publication_history _ _)
    | (driver_history_head TxSource.Ops.step; exact focused_history _)
    | (driver_history_head TxSource.Ops.access; exact focused_history _)
    | (driver_history_head TxSource.Ops.enqueue; exact focused_history _)
    | driver_product_history_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
