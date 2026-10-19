import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingCreateRepayment
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateChecked

/-! Full actual creation has its own internal prefix certificate. Native
admission, counted refusal repayment and labelled free occurrences are joined
in their actual order; the original full endpoint carrier remains separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging.Creation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Staged.Obligations QueueHandoff HandshakeSecurity.StagedConservation
open CreateDisposal CompleteCarrier
set_option maxHeartbeats 600000

theorem create_cuts (pid : PeerId) (items : List SkbId)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ suffix,(runPrefix (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items) w history).2=history++suffix ∧
      Cuts CompleteProduct.Safe history suffix := by
  rw [Admission.final_factor]
  cases head : items.head? with
  | none=>
    have failed : runPrefix (Admission.actualOps.step (invariant "an empty ring item") : PrefixM CausalJournal.Event Unit)
        w history=(.error (.invariant "an empty ring item"),history) := by
      simpa only [Admission.actualOps,HandshakeSecurity.StagedDisposal.TxSource.observed,
        HandshakeSecurity.StagedDisposal.TxSource.Ops.focus,HandshakeSecurity.StagedDisposal.TxSource.native,
        List.map_nil,List.append_nil] using focusPrefix_suffix CausalJournal.txEvent CausalJournal.txEvent?
        (liftPrefix (liftWG (invariant "an empty ring item" : WG.M Unit)) : PrefixM TxDisposition.Event Unit)
        w history (.error (.invariant "an empty ring item")) [] (by simp only [List.append_nil]; rfl)
    rw [failed]
    exact ⟨[],by simp,Cuts.nil ⟨debts,.accounted _ _ _ _ before⟩⟩
  | some first=>
    simp only [runPrefix_bind]
    obtain ⟨access,extended,cuts⟩ := admission_cuts pid items before
    have admission := CompleteSource.admission_cases pid items before
    cases front : runPrefix (Admission.actual pid items) w history with
    | mk outcome middle=>
      rw [front] at admission extended
      change middle=history++access at extended
      cases outcome with
      | error stop=>exact ⟨access,extended,cuts⟩
      | ok out=>
        obtain ⟨ret,u⟩ := out
        simp only []
        rcases admission.2 with ⟨code,unpublished⟩ | ⟨code,queued⟩
        · have notOk : ret≠0 := by rcases code with rfl | rfl <;> decide
          have notPipe : ret≠-WG.EPIPE := by rcases code with rfl | rfl <;> decide
          have batch : PendingBatch middle ledger items := by rw [extended]; exact pending.append access
          obtain ⟨suffix,later,more⟩ := refusal_cuts pid items first ret notOk notPipe unpublished batch
          exact ⟨access++suffix,by simpa only [extended,List.append_assoc] using later,
            cuts.append (extended ▸ more)⟩
        · obtain ⟨v,finish,_⟩ := CreateEntry.accepted_tail pid items first ret code queued.entry
          rw [finish]
          exact ⟨access,extended,cuts⟩

/-- The full source prefix guarantee has the same incoming pending batch and
restores the same caller debts/locals as the native endpoint theorem. -/
theorem create (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) :
    StateEnsures (fun h w _=>Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w ∧
      PendingBatch h ledger items) CompleteProduct.Safe (CausalJournal.create pid items)
      (fun _=>Carrier debts locals) := by
  apply StateEnsures.of_cuts (CompleteCreate.checked ledger debts locals pid items CompleteProduct.Safe
    (fun ledger locals h w before=>⟨debts,.accounted ledger locals h w before⟩))
  intro w a h before
  obtain ⟨suffix,grown,cuts⟩ := create_cuts pid items (w:=NativeAdapter.world w a) before.1 before.2
  have lowered := NativeAdapter.run_lower
    (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items) w a h
  change runStatePrefix (CausalJournal.create pid items) w a h=_ at lowered
  exact ⟨suffix,by rw [lowered]; exact grown,cuts⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging.Creation
