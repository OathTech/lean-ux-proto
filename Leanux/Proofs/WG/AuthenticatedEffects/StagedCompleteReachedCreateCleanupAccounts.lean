import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateCleanupSource

/-! The original refusal path derives its unpublished batch and each ordered
cleanup entry on the same successor ledger. Accepted creation cannot enter
this loop. No successful caller or pre-supplied child account is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open AllocatedObligation CreateDisposal CompleteCarrier CreatePoints CreatePhase
open HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

theorem accepted_no_cleanup (code : ret=0 ∨ ret = -WG.EPIPE)
    (before : Accounted h ledger debts active w.wg)
    (performed : runPrefix (beforeFree pid first ret) w h=(.ok (true,v),last)) : False := by
  rw [beforeFree_release_factor,runPrefix_bind] at performed
  obtain ⟨u,tested,atPipe⟩:=CreateEntry.guard_entry .createDataOk (ret == 0) before.entry
  rw [tested] at performed
  rcases code with rfl | rfl
  · simp [runPrefix_pure] at performed
  · simp only [show ((-WG.EPIPE : Int)==0)=false from rfl,Bool.false_eq_true,ite_false,runPrefix_bind] at performed
    obtain ⟨q,piped,_⟩:=CreateEntry.guard_entry .createDataOkEpipe ((-WG.EPIPE : Int)== -WG.EPIPE) atPipe
    rw [piped] at performed
    simp [runPrefix_pure] at performed

theorem Entry.accounted (entry : Entry pid items w h ret v last)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch h ledger items) :
    ∃next,Staged.Obligations.Step ledger next ∧ PendingBatch last next items ∧
      Accounted last next debts (⟨.unpublished,pid,items⟩::locals) v.wg := by
  cases entry with
  | @reached first ret u v middle last head admitted repaid=>
    have front:=CompleteSource.admission_cases pid items before
    rw [admitted] at front
    rcases front.2 with ⟨_,unpublished⟩ | ⟨code,queued⟩
    · have repayment:=CompleteCreate.repayment_cases pid first ret unpublished
      rw [repaid] at repayment
      obtain ⟨next,step,frame,_,account⟩:=repayment
      obtain ⟨frontSuffix,frontGrown⟩:=Admission.actual_appends pid items w h
      rw [admitted] at frontGrown
      change middle=h++frontSuffix at frontGrown
      obtain ⟨suffix,grown⟩:=beforeFree_appends pid first ret u middle
      rw [repaid] at grown
      change last=middle++suffix at grown
      have atFront : PendingBatch middle ledger items:=frontGrown ▸ pending.append frontSuffix
      exact ⟨next,step,grown ▸ (atFront.allocated_frame frame).append suffix,account⟩
    · exact False.elim (accepted_no_cleanup code queued repaid)

theorem Cursor.progress (cursor : Cursor reason remaining w h skb rest u middle)
    (steps : Staged.Obligations.Step rootLedger ledger)
    (ordered : items=done++remaining) (settled : AllDropped h ledger reason done)
    (pending : PendingBatch h ledger remaining)
    (before : Accounted h ledger debts (⟨.unpublished,pid,remaining⟩::locals) w.wg) :
    ∃next doneNext,Staged.Obligations.Step rootLedger next ∧ items=doneNext++(skb::rest) ∧
      AllDropped middle next reason doneNext ∧ PendingBatch middle next (skb::rest) ∧
      Accounted middle next debts (⟨.unpublished,pid,skb::rest⟩::locals) u.wg := by
  induction cursor generalizing ledger done with
  | here=>exact ⟨ledger,done,steps,ordered,settled,pending,before⟩
  | @later skb tail head rest w q u h prior middle completed cursor ih=>
    obtain ⟨cut⟩:=free_cut reason before pending
    rw [cut.original] at completed
    cases completed
    apply ih (steps.trans cut.step) (done:=done++[head])
    · simpa only [List.append_assoc,List.singleton_append] using ordered
    · intro id member
      rcases List.mem_append.mp member with old | current
      · exact (settled id old).transport _ cut.step
      · cases List.mem_singleton.mp current
        exact cut_dropped cut
    · exact cut_pending cut pending
    · exact cut.accounted

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateCleanup
