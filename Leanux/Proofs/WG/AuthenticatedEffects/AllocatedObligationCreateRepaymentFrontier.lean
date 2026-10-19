import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateRepaymentFrames

/-! The actual refusal guards and repayments retain the fixed ledger at the
last reached source cut. A nested final release may settle staged obligations;
its successor is carried forward into the packet-free loop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations QueueHandoff
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
      (owned : Owned ledger debts locals history v) (bounded : Packets.Inv v.wg)
      (failed : runPrefix (keyRepayment first) v history = (.error stop,last))
  | peerStopped (u v z : World) (keyHistory : List CausalJournal.Event)
      (accepted : runPrefix (Admission.actualOps.step (branch .createDataOk (ret == 0))) w history =
        (.ok (false,u),history))
      (pipe : runPrefix (Admission.actualOps.step (branch .createDataOkEpipe (ret == -WG.EPIPE))) u history =
        (.ok (false,v),history))
      (key : runPrefix (keyRepayment first) v history = (.ok ((),z),keyHistory))
      (frontier : PeerRelease.Frontier ledger debts locals (some pid) z keyHistory stop last)

def RepaymentReturned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (cleanup : Bool) (history : List CausalJournal.Event) (w : World) : Prop :=
  ∃ after, Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
    (cleanup = false → after = ledger) ∧ Owned after debts locals history w ∧ Packets.Inv w.wg

/-- Every original repayment either returns a complete owned successor ledger
or identifies its exact stopped key/peer callback and reached owner cut. In
particular final peer disposal is never replaced by unchanged-ledger framing. -/
theorem beforeFree_cases (pid : PeerId) (first : SkbId) (ret : Int)
    (owned : Owned ledger debts locals history w) (bounded : Packets.Inv w.wg) :
    match (runPrefix (beforeFree pid first ret) w history).1 with
    | .error stop => RepaymentStop ledger debts locals pid first ret w history stop
        (runPrefix (beforeFree pid first ret) w history).2
    | .ok (cleanup,v) => RepaymentReturned ledger debts locals cleanup
        (runPrefix (beforeFree pid first ret) w history).2 v := by
  rw [beforeFree_release_factor]
  simp only [runPrefix_bind]
  obtain ⟨u,accepted,atFirst,boundsFirst⟩ := guard_total .createDataOk (ret == 0) owned bounded
  rw [accepted]
  cases yes : (ret == 0) with
  | true =>
    simp only [ite_true,runPrefix_pure]
    exact ⟨ledger,.refl _,.refl _,fun _ => rfl,atFirst,boundsFirst⟩
  | false =>
    simp only [Bool.false_eq_true,ite_false,runPrefix_bind]
    obtain ⟨v,pipe,atKey,boundsKey⟩ := guard_total .createDataOkEpipe (ret == -WG.EPIPE) atFirst boundsFirst
    rw [pipe]
    cases isPipe : (ret == -WG.EPIPE) with
    | true =>
      simp only [ite_true,runPrefix_pure]
      exact ⟨ledger,.refl _,.refl _,fun _ => rfl,atKey,boundsKey⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false,runPrefix_bind]
      cases key : runPrefix (keyRepayment first) v history with
      | mk outcome keyHistory =>
        cases outcome with
        | error stop =>
          exact .keyStopped u v (by simpa [yes] using accepted)
            (by simpa [isPipe] using pipe) atKey boundsKey key
        | ok out =>
          obtain ⟨ignored,z⟩ := out
          cases ignored
          obtain ⟨atPeer,boundsPeer⟩ := key_repayment_returned first atKey boundsKey key
          have casesPeer := PeerRelease.actual_cases (some pid) atPeer boundsPeer
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
              obtain ⟨value,g,a,cutHistory,after,_,_,step,frame,_,finalOwned,finalBounds⟩ := casesPeer
              exact ⟨after,step,frame,(by intro impossible; cases impossible),finalOwned,finalBounds⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
