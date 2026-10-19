import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationDeadEntryHistoryFrames

/-! Cached key and peer repayment follow the DEAD free loop. A final peer
release may settle staged obligations; its exact successor entry survives. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations
set_option pp.structureInstances false

inductive RepayStop (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (key : KeypairId) (w : World) (history : List CausalJournal.Event)
    (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | keyStopped (entry : StagedEntry.Inv history ledger debts locals w.wg)
      (failed : runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false))
        w history = (.error stop,last))
  | peerStopped (u : World) (middle : List CausalJournal.Event)
      (keyRun : runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false))
        w history = (.ok ((),u),middle))
      (frontier : StagedEntry.Release.Frontier ledger debts locals (some pid) u middle stop last)

def RepayReturned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (value : Bool) (history : List CausalJournal.Event) (w : World) : Prop :=
  value = true ∧ ∃ afterLedger, Staged.Obligations.Step ledger afterLedger ∧
    StagedEntry.Inv history afterLedger debts locals w.wg

theorem repay_cases (pid : PeerId) (key : KeypairId)
    (before : StagedEntry.Inv history ledger debts locals w.wg) :
    match (runPrefix (repay pid key) w history).1 with
    | .error stop => RepayStop ledger debts locals pid key w history stop (runPrefix (repay pid key) w history).2
    | .ok (value,v) => RepayReturned ledger debts locals value (runPrefix (repay pid key) w history).2 v := by
  unfold repay
  simp only [runPrefix_bind]
  cases keyRun : runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false)) w history with
  | mk outcome middle =>
    cases outcome with
    | error stop => exact .keyStopped before keyRun
    | ok out =>
      obtain ⟨ignored,u⟩ := out
      cases ignored
      have atRelease := key_entry key before keyRun
      have released := StagedEntry.Release.actual_cases (some pid) atRelease
      simp only []
      cases peerRun : runPrefix (Admission.actualOps.release (some pid)) u middle with
      | mk result last =>
        rw [peerRun] at released
        cases result with
        | error stop => exact .peerStopped u middle keyRun released
        | ok out =>
          obtain ⟨ignored,v⟩ := out
          cases ignored
          simp only [runPrefix_pure]
          obtain ⟨value,g,a,cutHistory,afterLedger,_,_,step,_,_,entry⟩ := released
          exact ⟨rfl,afterLedger,step,entry⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
