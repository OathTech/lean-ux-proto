import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDisposalChecked

/-! The actual refusal guards and repayments carry paired accounting at each
reached source cut. A final peer release settles staged obligations on the
same successor shared by Entry and Complete before the free loop starts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation
open Staged.Obligations QueueHandoff CreateDisposal CompleteCarrier
open StagedTerminalComplete
set_option pp.structureInstances false
set_option maxHeartbeats 600000

inductive RepaymentStop (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (first : SkbId) (ret : Int) (w : World) (history : List CausalJournal.Event)
    (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | keyStopped (u v : World)
      (accepted : runPrefix (Admission.actualOps.step (branch .createDataOk (ret == 0))) w history =
        (.ok (false,u),history))
      (pipe : runPrefix (Admission.actualOps.step (branch .createDataOkEpipe (ret == -WG.EPIPE))) u history =
        (.ok (false,v),history))
      (owned : Accounted history ledger debts locals v.wg)
      (complete : Complete last ledger)
      (failed : runPrefix (keyRepayment first) v history = (.error stop,last))
  | peerStopped (u v z : World) (keyHistory : List CausalJournal.Event)
      (accepted : runPrefix (Admission.actualOps.step (branch .createDataOk (ret == 0))) w history =
        (.ok (false,u),history))
      (pipe : runPrefix (Admission.actualOps.step (branch .createDataOkEpipe (ret == -WG.EPIPE))) u history =
        (.ok (false,v),history))
      (key : runPrefix (keyRepayment first) v history = (.ok ((),z),keyHistory))
      (frontier : StagedTerminalComplete.Source.Nested.Frontier ledger debts locals (some pid) z keyHistory stop last)

def RepaymentReturned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (ret : Int) (cleanup : Bool) (history : List CausalJournal.Event) (w : World) : Prop :=
  ∃ after, Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
    (cleanup = false → after = ledger ∧ (ret = 0 ∨ ret = -WG.EPIPE)) ∧
    Accounted history after debts locals w.wg

/-- Every original repayment either returns the paired semantic successor ledger
or identifies its exact stopped key/peer callback and reached owner cut. In
particular final peer disposal is never replaced by unchanged-ledger framing. -/
theorem repayment_cases (pid : PeerId) (first : SkbId) (ret : Int)
    (owned : Accounted history ledger debts locals w.wg) :
    match (runPrefix (beforeFree pid first ret) w history).1 with
    | .error stop => RepaymentStop ledger debts locals pid first ret w history stop
        (runPrefix (beforeFree pid first ret) w history).2
    | .ok (cleanup,v) => RepaymentReturned ledger debts locals ret cleanup
        (runPrefix (beforeFree pid first ret) w history).2 v := by
  rw [beforeFree_release_factor]
  simp only [runPrefix_bind]
  obtain ⟨u,accepted,atFirst⟩ := CreateEntry.guard_entry .createDataOk (ret == 0) owned.entry
  rw [accepted]
  cases yes : (ret == 0) with
  | true =>
    simp only [ite_true,runPrefix_pure]
    exact ⟨ledger,.refl _,.refl _,fun _ => ⟨rfl,Or.inl (by simpa using yes)⟩,atFirst,owned.complete⟩
  | false =>
    simp only [Bool.false_eq_true,ite_false,runPrefix_bind]
    obtain ⟨v,pipe,atKey⟩ := CreateEntry.guard_entry .createDataOkEpipe (ret == -WG.EPIPE) atFirst
    rw [pipe]
    cases isPipe : (ret == -WG.EPIPE) with
    | true =>
      simp only [ite_true,runPrefix_pure]
      exact ⟨ledger,.refl _,.refl _,fun _ => ⟨rfl,Or.inr (by simpa using isPipe)⟩,atKey,owned.complete⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false,runPrefix_bind]
      obtain ⟨_,_,keyComplete,_⟩ := key_history first v history owned.complete
      cases key : runPrefix (keyRepayment first) v history with
      | mk outcome keyHistory =>
        rw [key] at keyComplete
        cases outcome with
        | error stop =>
          exact .keyStopped u v (by simpa [yes] using accepted)
            (by simpa [isPipe] using pipe) ⟨atKey,owned.complete⟩ keyComplete key
        | ok out =>
          obtain ⟨ignored,z⟩ := out
          cases ignored
          have atPeer := CreateEntry.key_repayment_entry first atKey key
          have casesPeer := StagedTerminalComplete.Source.Nested.actual_cases (some pid) atPeer keyComplete
          simp only []
          cases peer : runPrefix (Admission.actualOps.release (some pid)) z keyHistory with
          | mk result last =>
            rw [peer] at casesPeer
            cases result with
            | error stop =>
              exact .peerStopped u v z keyHistory (by simpa [yes] using accepted)
                (by simpa [isPipe] using pipe) key casesPeer
            | ok out =>
              obtain ⟨ignored,final⟩ := out
              cases ignored
              simp only [runPrefix_pure]
              obtain ⟨value,g,a,cutHistory,after,_,_,step,frame,_,finalOwned,finished⟩ := casesPeer
              exact ⟨after,step,frame,(by intro impossible; cases impossible),finalOwned,finished⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
