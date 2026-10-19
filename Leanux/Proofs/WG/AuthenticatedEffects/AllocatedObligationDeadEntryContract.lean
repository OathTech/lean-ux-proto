import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationDeadEntryRepayment

/-! Whole native DEAD disposal retains all first-terminal cuts even when the
later cached key or peer repayment Stops. The source free loop is total under
the exact selected ownership and pending-ticket assignment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal HandshakeSecurity.StagedConservation
set_option pp.structureInstances false

inductive DeadStop (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
    (history : List CausalJournal.Event) (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | atRepay (u : World) (suffix : List CausalJournal.Event) (afterFree : Ledger)
      (freed : runPrefix (loop (.deadBatch pid head) items) w history = (.ok ((),u),history ++ suffix))
      (step : Staged.Obligations.Step ledger afterFree)
      (entry : StagedEntry.Inv (history ++ suffix) afterFree debts locals u.wg)
      (dropped : AllDropped (history ++ suffix) afterFree (.deadBatch pid head) items)
      (frontier : RepayStop afterFree debts locals pid head.keypair u (history ++ suffix) stop last)

def DeadReturned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (value : Bool)
    (history : List CausalJournal.Event) (w : World) : Prop :=
  value = true ∧ ∃ afterLedger, Staged.Obligations.Step ledger afterLedger ∧
    StagedEntry.Inv history afterLedger debts locals w.wg ∧
    AllDropped history afterLedger (.deadBatch pid head) items

/-- Every selected DEAD packet receives its named native terminal and is
freed before key/peer repayment. Normal return restores the caller's exact
debts and locals; Stop retains the completed drops and the real failed
repayment cut, never replacing it by an assumed completed enclosing worker. -/
theorem dead_cases (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : StagedEntry.Inv history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    match (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).1 with
    | .error stop => DeadStop ledger debts locals pid items head w history stop
        (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
          CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).2
    | .ok (value,v) => DeadReturned ledger debts locals pid items head value
        (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
          CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).2 v := by
  rw [dead_factor,runPrefix_bind]
  obtain ⟨u,suffix,afterFree,freed,step,atRepay,dropped⟩ :=
    loop_entry_total_exact (.deadBatch pid head) .selected items before pending
  rw [freed]
  simp only []
  have result := repay_cases pid head.keypair atRepay
  cases performed : runPrefix (repay pid head.keypair) u (history ++ suffix) with
  | mk outcome last =>
    rw [performed] at result
    cases outcome with
    | error stop => exact .atRepay u suffix afterFree freed step atRepay dropped result
    | ok out =>
      obtain ⟨value,v⟩ := out
      obtain ⟨truth,afterLedger,steps,final⟩ := result
      obtain ⟨repaid,extended⟩ := repay_appends pid head.keypair u (history ++ suffix)
      rw [performed] at extended
      change last = (history ++ suffix) ++ repaid at extended
      refine ⟨truth,afterLedger,step.trans steps,final,?_⟩
      rw [extended]
      exact fun id member => (dropped id member).transport repaid steps

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
