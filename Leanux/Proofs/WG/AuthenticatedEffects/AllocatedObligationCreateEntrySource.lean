import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryFront
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryAccepted
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateDebtTail

/-! Full entry transport through the actual create callback. Its stopped
alternatives retain the reached native owner cut; normal refusal consumes the
same pending batch and restores the caller's original debts and locals. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal HandshakeSecurity.StagedConservation
set_option pp.structureInstances false
set_option maxHeartbeats 600000

inductive CreatedStop (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (w : World) (history : List CausalJournal.Event)
    (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | emptyStopped (empty : items.head? = none)
      (before : StagedEntry.Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
      (failed : runPrefix (Admission.actualOps.step (invariant "an empty ring item") : PrefixM CausalJournal.Event Unit)
        w history = (.error stop,last))
  | frontStopped (first : SkbId) (head : items.head? = some first)
      (frontier : FrontStop ledger debts locals pid items w history stop last)
  | repaymentStopped (first : SkbId) (ret : Int) (u : World) (middle : List CausalJournal.Event)
      (head : items.head? = some first)
      (admission : runPrefix (Admission.actual pid items) w history = (.ok (ret,u),middle))
      (code : ret = -EINVAL ∨ ret = -WG.ENOSPC)
      (frontier : RepaymentStop ledger debts (⟨.unpublished,pid,items⟩ :: locals)
        pid first ret u middle stop last)

def CreatedReturned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (w : World) (history : List CausalJournal.Event)
    (last : List CausalJournal.Event) (v : World) : Prop :=
  ∃ first ret u middle afterLedger,
    items.head? = some first ∧
    runPrefix (Admission.actual pid items) w history = (.ok (ret,u),middle) ∧
    Staged.Obligations.Step ledger afterLedger ∧
    StagedEntry.Inv last afterLedger debts locals v.wg ∧
    (((ret = 0 ∨ ret = -WG.EPIPE) ∧ afterLedger = ledger) ∨
      ((ret = -EINVAL ∨ ret = -WG.ENOSPC) ∧
        AllDropped last afterLedger (.createRefused pid ret) items))

/-- Every original create execution retains full fixed-ticket ownership on
Stop. A normal return either transfers the batch to its real peer queue or
settles all its packets at their own named disposal cuts; the exact original
debt list and caller locals are restored in either case. -/
theorem create_cases (pid : PeerId) (items : List SkbId)
    (before : StagedEntry.Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    match (runPrefix (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items) w history).1 with
    | .error stop => CreatedStop ledger debts locals pid items w history stop
        (runPrefix (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
          CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items) w history).2
    | .ok ((),v) => CreatedReturned ledger debts locals pid items w history
        (runPrefix (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
          CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items) w history).2 v := by
  rw [Admission.final_factor]
  cases head : items.head? with
  | none =>
    simp only
    have failed : runPrefix (Admission.actualOps.step (invariant "an empty ring item") : PrefixM CausalJournal.Event Unit)
        w history = (.error (.invariant "an empty ring item"),history) := by
      simpa only [Admission.actualOps,HandshakeSecurity.StagedDisposal.TxSource.observed,
        HandshakeSecurity.StagedDisposal.TxSource.Ops.focus,HandshakeSecurity.StagedDisposal.TxSource.native,
        List.map_nil,List.append_nil] using focusPrefix_suffix CausalJournal.txEvent CausalJournal.txEvent?
        (liftPrefix (liftWG (invariant "an empty ring item" : WG.M Unit)) : PrefixM TxDisposition.Event Unit)
        w history (.error (.invariant "an empty ring item")) [] (by simp only [List.append_nil]; rfl)
    rw [failed]
    exact .emptyStopped head before failed
  | some first =>
    simp only [runPrefix_bind]
    have admission := front_cases pid items before
    cases front : runPrefix (Admission.actual pid items) w history with
    | mk outcome middle =>
      rw [front] at admission
      cases outcome with
      | error stop => exact .frontStopped first head admission
      | ok out =>
        obtain ⟨ret,u⟩ := out
        simp only []
        rcases admission with ⟨code,unpublished⟩ | ⟨code,queued⟩
        · have notOk : ret ≠ 0 := by rcases code with rfl | rfl <;> decide
          have notPipe : ret ≠ -WG.EPIPE := by rcases code with rfl | rfl <;> decide
          obtain ⟨suffix,extended⟩ := Admission.actual_appends pid items w history
          rw [front] at extended
          change middle = history ++ suffix at extended
          have batch : PendingBatch middle ledger items := by
            rw [extended]
            exact pending.append suffix
          have tail := refused_tail_exact pid items first ret notOk notPipe unpublished batch
          change (match (runPrefix (Admission.tail Admission.actualOps free pid items first ret) u middle).1 with
            | .error stop => CreatedStop ledger debts locals pid items w history stop
                (runPrefix (Admission.tail Admission.actualOps free pid items first ret) u middle).2
            | .ok ((),v) => CreatedReturned ledger debts locals pid items w history
                (runPrefix (Admission.tail Admission.actualOps free pid items first ret) u middle).2 v)
          cases finish : runPrefix (Admission.tail Admission.actualOps free pid items first ret) u middle with
          | mk result last =>
            rw [finish] at tail
            cases result with
            | error stop => exact .repaymentStopped first ret u middle head front code tail
            | ok out =>
              obtain ⟨ignored,v⟩ := out
              cases ignored
              obtain ⟨afterLedger,step,final,dropped⟩ := tail
              exact ⟨first,ret,u,middle,afterLedger,head,front,step,final,Or.inr ⟨code,dropped⟩⟩
        · obtain ⟨v,finish,final⟩ := accepted_tail pid items first ret code queued
          change (match (runPrefix (Admission.tail Admission.actualOps free pid items first ret) u middle).1 with
            | .error stop => CreatedStop ledger debts locals pid items w history stop
                (runPrefix (Admission.tail Admission.actualOps free pid items first ret) u middle).2
            | .ok ((),v) => CreatedReturned ledger debts locals pid items w history
                (runPrefix (Admission.tail Admission.actualOps free pid items first ret) u middle).2 v)
          rw [finish]
          exact ⟨first,ret,u,middle,ledger,head,front,.refl _,final,Or.inl ⟨code,rfl⟩⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
