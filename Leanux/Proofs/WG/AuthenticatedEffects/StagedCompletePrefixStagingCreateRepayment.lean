import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingCreateLoop
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateTail

/-! Refusal repayment prefixes follow the actual key-access and counted peer
release before the per-packet free loop. The latter starts on that same successor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging.Creation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Staged.Obligations QueueHandoff HandshakeSecurity.StagedConservation
open CreateDisposal CompleteCarrier StagedTerminalComplete
set_option maxHeartbeats 600000

theorem key_cuts (first : SkbId) (before : Accounted h ledger debts locals w.wg) :
    ∃ suffix,(runPrefix (keyRepayment first) w h).2=h++suffix ∧ Cuts CompleteProduct.Safe h suffix := by
  let Good := fun current=>∃ prior,current=h++prior ∧ ∀ event∈prior,birthPackets event=[] ∧ Quiet event
  have rule : Driver.ProductHistorySafe Good (keyRepayment first) := by
    unfold keyRepayment
    exact Driver.History.product_bind (focused Good (quiet_growth h) _)
      (fun _=>focused Good (quiet_growth h) _)
  obtain ⟨_,_,⟨suffix,same,quiet⟩,_⟩ := rule w h ⟨[],by simp,by simp⟩
  exact ⟨suffix,same,CompletePrefix.quiet_cuts before
    (fun event member=>(quiet event member).1) (fun event member=>(quiet event member).2)⟩

theorem repayment_cuts (pid : PeerId) (first : SkbId) (ret : Int)
    (before : Accounted history ledger debts locals w.wg) :
    ∃ suffix,(runPrefix (beforeFree pid first ret) w history).2=history++suffix ∧
      Cuts CompleteProduct.Safe history suffix := by
  rw [beforeFree_release_factor]
  simp only [runPrefix_bind]
  obtain ⟨u,accepted,atFirst⟩ := CreateEntry.guard_entry .createDataOk (ret == 0) before.entry
  rw [accepted]
  cases yes : (ret == 0) with
  | true=>
    simp only [ite_true,runPrefix_pure]
    exact ⟨[],by simp,Cuts.nil ⟨debts,.accounted _ _ _ _ before⟩⟩
  | false=>
    simp only [Bool.false_eq_true,ite_false,runPrefix_bind]
    obtain ⟨v,pipe,atKey⟩ := CreateEntry.guard_entry .createDataOkEpipe (ret == -WG.EPIPE) atFirst
    rw [pipe]
    cases isPipe : (ret == -WG.EPIPE) with
    | true=>
      simp only [ite_true,runPrefix_pure]
      exact ⟨[],by simp,Cuts.nil ⟨debts,.accounted _ _ _ _ before⟩⟩
    | false=>
      simp only [Bool.false_eq_true,ite_false,runPrefix_bind]
      obtain ⟨access,extended,cuts⟩ := key_cuts first (show Accounted history ledger debts locals v.wg from
        ⟨atKey,before.complete⟩)
      obtain ⟨_,_,keyComplete,_⟩ := CompleteCreate.key_history first v history before.complete
      cases key : runPrefix (keyRepayment first) v history with
      | mk outcome keyHistory=>
        rw [key] at extended keyComplete
        change keyHistory=history++access at extended
        cases outcome with
        | error stop=>exact ⟨access,extended,cuts⟩
        | ok out=>
          obtain ⟨ignored,z⟩ := out
          cases ignored
          have atPeer := CreateEntry.key_repayment_entry first atKey key
          obtain ⟨later,extension,more⟩ := Disposal.nested_cuts (some pid) CompleteProduct.Safe
            (fun ledger h w account=>⟨debts,.accounted ledger locals h w account⟩) z keyHistory
            ⟨ledger,atPeer,keyComplete⟩
          simp only []
          cases released : runPrefix (Admission.actualOps.release (some pid)) z keyHistory with
          | mk result last=>
            rw [released] at extension
            change last=keyHistory++later at extension
            cases result with
            | error stop=>
              exact ⟨access++later,by simp only [extension,extended,List.append_assoc],
                cuts.append (extended ▸ more)⟩
            | ok out=>
              obtain ⟨ignored,final⟩ := out
              cases ignored
              simp only [runPrefix_pure]
              exact ⟨access++later,by simp only [extension,extended,List.append_assoc],
                cuts.append (extended ▸ more)⟩

theorem refusal_cuts (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int)
    (notOk : ret≠0) (notPipe : ret≠-WG.EPIPE)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ suffix,(runPrefix (Admission.tail Admission.actualOps free pid items first ret) w history).2=history++suffix ∧
      Cuts CompleteProduct.Safe history suffix := by
  rw [tail_factor,runPrefix_bind]
  have repayment := CompleteCreate.repayment_cases pid first ret before
  obtain ⟨access,extended,cuts⟩ := repayment_cuts pid first ret before
  cases performed : runPrefix (beforeFree pid first ret) w history with
  | mk outcome middle=>
    rw [performed] at repayment extended
    change middle=history++access at extended
    cases outcome with
    | error stop=>exact ⟨access,extended,cuts⟩
    | ok out=>
      obtain ⟨cleanup,u⟩ := out
      obtain ⟨releaseLedger,_,frame,accepted,atLoop⟩ := repayment
      cases cleanup with
      | false=>
        rcases (accepted rfl).2 with ok | pipe
        · exact False.elim (notOk ok)
        · exact False.elim (notPipe pipe)
      | true=>
        have batch : PendingBatch middle releaseLedger items := by
          rw [extended]
          exact (pending.allocated_frame frame).append access
        obtain ⟨v,suffix,afterLedger,freeRun,later,_,_⟩ :=
          free_loop_cuts (.createRefused pid ret) .unpublished items atLoop batch
        simp only [ite_true]
        rw [freeRun]
        exact ⟨access++suffix,by simp only [extended,List.append_assoc],cuts.append (extended ▸ later)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging.Creation
