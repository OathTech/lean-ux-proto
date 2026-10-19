import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointFreeLoop
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointEntries

/-! The actual refused admission supplies the loop's ordered pending cohort.
Key/peer repayments run before it; counted final release can change the
ledger, so the loop uses that exact successor and its allocated frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

def refusalPrefix (pid : PeerId) (items : List SkbId) (first : SkbId) : PrefixM CausalJournal.Event (Int×Bool) := do
  let ret ← Admission.actual pid items
  let cleanup ← beforeFree pid first ret
  return (ret,cleanup)

theorem refused_accounted
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (admitted : runPrefix (Admission.actual pid items) w history=(.ok (ret,u),middle))
    (code : ret = -EINVAL ∨ ret = -WG.ENOSPC) :
    Accounted middle ledger debts (⟨.unpublished,pid,items⟩::locals) u.wg := by
  have result:=CompleteSource.admission_cases pid items before
  rw [admitted] at result
  rcases result.2 with ⟨_,account⟩ | ⟨accepted,_⟩
  · exact account
  · rcases code with rfl | rfl <;> rcases accepted with impossible | impossible <;> cases impossible

/-- All loop-entry assumptions follow from the original admission and the
actual repayment's returned successor, including unchanged allocated tickets
and the same original list order. -/
theorem refusal_loop_entry
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items)
    (admitted : runPrefix (Admission.actual pid items) w history=(.ok (ret,u),middle))
    (code : ret = -EINVAL ∨ ret = -WG.ENOSPC)
    (repaid : runPrefix (beforeFree pid first ret) u middle=(.ok (true,v),last)) :
    ∃ next, Staged.Obligations.Step ledger next ∧ AllocatedFrame ledger next ∧
      Accounted last next debts (⟨.unpublished,pid,items⟩::locals) v.wg ∧
      PendingBatch last next items ∧
      runPrefix (refusalPrefix pid items first) w history=(.ok ((ret,true),v),last) := by
  have initial:=refused_accounted before admitted code
  have payment:=CompleteCreate.repayment_cases pid first ret initial
  rw [repaid] at payment
  obtain ⟨next,step,frame,_,account⟩:=payment
  obtain ⟨front,grown⟩:=Admission.actual_appends pid items w history
  rw [admitted] at grown
  change middle=history++front at grown
  obtain ⟨suffix,extended⟩:=beforeFree_appends pid first ret u middle
  rw [repaid] at extended
  change last=middle++suffix at extended
  refine ⟨next,step,frame,account,?_,?_⟩
  · rw [extended,grown]
    exact ((pending.allocated_frame frame).append front).append suffix
  · simp only [refusalPrefix,runPrefix_bind,admitted,repaid,runPrefix_pure]

theorem refusal_residual (head : items.head?=some first)
    (admitted : runPrefix (Admission.actual pid items) w history=(.ok (ret,u),middle))
    (repaid : runPrefix (beforeFree pid first ret) u middle=(.ok (true,v),last)) :
    runPrefix (body pid items) w history=runPrefix (loop (.createRefused pid ret) items) v last := by
  rw [body,Admission.final_factor,head,runPrefix_bind,admitted]
  simp only
  rw [tail_factor,runPrefix_bind,repaid]
  rfl

/-- Every refused source that reaches its free loop has a total ordered native
walk; each internal erase is exposed by FreeCursor.pending_receipt. Refusal
stops before that cut remain the original key/peer child frontiers. -/
theorem refusal_walk (head : items.head?=some first)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items)
    (admitted : runPrefix (Admission.actual pid items) w history=(.ok (ret,u),middle))
    (code : ret = -EINVAL ∨ ret = -WG.ENOSPC)
    (repaid : runPrefix (beforeFree pid first ret) u middle=(.ok (true,v),last)) :
    ∃ next finalWorld finalHistory final,
      Staged.Obligations.Step ledger next ∧
      Nonempty (FreeWalk (.createRefused pid ret) pid debts locals items v last next finalWorld finalHistory final) ∧
      runPrefix (body pid items) w history=(.ok ((),finalWorld),finalHistory) ∧
      Accounted finalHistory final debts locals finalWorld.wg := by
  obtain ⟨next,step,_,account,batch,_⟩:=refusal_loop_entry before pending admitted code repaid
  obtain ⟨finalWorld,finalHistory,final,⟨walk⟩⟩:=free_walk account batch
  exact ⟨next,finalWorld,finalHistory,final,step,⟨walk⟩,
    (refusal_residual head admitted repaid).trans walk.run,walk.accounted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
