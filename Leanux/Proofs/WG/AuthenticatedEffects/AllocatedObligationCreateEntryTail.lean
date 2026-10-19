import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryRepayment

/-! The actual refusal tail composes full repayment and packet-free entries.
A stopped repayment retains its exact source frontier; successful repayment
cannot lose staged dispositions before the complete native free loop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations QueueHandoff CreateDisposal HandshakeSecurity.StagedConservation
set_option pp.structureInstances false

def RefusalReturned (ledger : Ledger) (locals : List TxLocalBatch) (reason : Terminal.Reason)
    (items : List SkbId) (history : List CausalJournal.Event) (w : World) : Prop :=
  ∃ afterLedger afterDebts, Staged.Obligations.Step ledger afterLedger ∧
    StagedEntry.Inv history afterLedger afterDebts locals w.wg ∧
    AllDropped history afterLedger reason items

/-- Every actual refusal tail either stops at its original repayment frontier
or returns the full canonical entry with every selected packet settled at its
own named native free. The same pending tickets and physical local are used
throughout; no enclosing create-success premise is assumed. -/
theorem refused_tail (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int)
    (notOk : ret ≠ 0) (notPipe : ret ≠ -WG.EPIPE)
    (before : StagedEntry.Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    match (runPrefix (Admission.tail Admission.actualOps free pid items first ret) w history).1 with
    | .error stop => RepaymentStop ledger debts (⟨.unpublished,pid,items⟩ :: locals)
        pid first ret w history stop
        (runPrefix (Admission.tail Admission.actualOps free pid items first ret) w history).2
    | .ok ((),v) => RefusalReturned ledger locals (.createRefused pid ret) items
        (runPrefix (Admission.tail Admission.actualOps free pid items first ret) w history).2 v := by
  rw [tail_factor,runPrefix_bind]
  have repayment := beforeFree_cases pid first ret before
  cases performed : runPrefix (beforeFree pid first ret) w history with
  | mk outcome middle =>
    rw [performed] at repayment
    cases outcome with
    | error stop => exact repayment
    | ok out =>
      obtain ⟨cleanup,u⟩ := out
      obtain ⟨releaseLedger,step,frame,accepted,atLoop⟩ := repayment
      cases cleanup with
      | false =>
        rcases (accepted rfl).2 with ok | pipe
        · exact False.elim (notOk ok)
        · exact False.elim (notPipe pipe)
      | true =>
        obtain ⟨repaid,extended⟩ := beforeFree_appends pid first ret w history
        rw [performed] at extended
        change middle = history ++ repaid at extended
        have batch : PendingBatch middle releaseLedger items := by
          rw [extended]
          exact (pending.allocated_frame frame).append repaid
        obtain ⟨v,suffix,afterLedger,afterDebts,freeRun,steps,final,dropped⟩ :=
          loop_entry_total (.createRefused pid ret) .unpublished items atLoop batch
        simp only [ite_true]
        rw [freeRun]
        exact ⟨afterLedger,afterDebts,step.trans steps,final,dropped⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
