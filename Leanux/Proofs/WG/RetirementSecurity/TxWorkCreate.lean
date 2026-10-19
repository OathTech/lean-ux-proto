import Leanux.Proofs.WG.RetirementSecurity.TxWorkCleanup

/-! The complete native creation call establishes pending service for every
admitted owning batch and preserves all earlier service obligations. Refusal
cleanup consumes only the detached unpublished batch. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem Obligations.publish_return
    (before : Obligations (publicationPending ret items crypt) tx w)
    (inventory : TxInventory locals w) (a b : Ambient)
    (run : ((createPublishReturn items ret).run w).run a=.ok ((result,v),b)) :
    result=ret ∧ Obligations crypt tx v := by
  simp only [createPublishReturn,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨pipe,u,c,branchRun,tail⟩:=run
  have guard:pipe=(ret == -WG.EPIPE) ∧ u=w := by cases branchRun; exact ⟨rfl,rfl⟩
  obtain ⟨checked,same⟩:=guard
  subst u
  cases pipe with
  | false=>
    have notPipe:ret≠ -Leanux.EPIPE := by simpa [WG.EPIPE,Leanux.EPIPE] using checked.symm
    simp only [Bool.false_eq_true,ite_false] at tail
    cases tail
    exact ⟨rfl,by simpa only [publicationPending,ite_eq_right notPipe] using before⟩
  | true=>
    have isPipe:ret = -Leanux.EPIPE := by simpa [WG.EPIPE,Leanux.EPIPE] using checked.symm
    have pending:Obligations (items::crypt) tx w := by
      simpa only [publicationPending,ite_eq_left isPipe] using before
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,u,c,published,done⟩:=tail
    cases done
    exact ⟨rfl,pending.publish inventory .dead (by decide) _ b published⟩

theorem Obligations.create_return (before : Obligations crypt tx w)
    (inventory : TxInventory (⟨.unpublished,pid,items⟩::locals) w)
    (physical : TxDisposition.LiveFrontier.Physical w) (device : w.dev=some d)
    (a b : Ambient)
    (run : ((createReturnSource pid items).run w).run a=.ok ((ret,v),b)) :
    Obligations crypt tx v := by
  simp only [createReturnSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,peerRun,dead,t,e,branchRun,tail⟩:=run
  have same:=(Origins.getPeer_return pid w u p a c peerRun).1
  subst u
  have same:t=w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .createDataDead p.isDead) (fun t=>t=w))
      w c dead t e rfl branchRun
  subst t
  cases dead with
  | true=>simp only [ite_true] at tail; cases tail; exact before
  | false=>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨result,u,c,enqueueRun,publishRun⟩:=tail
    have pending:=before.admission inventory physical device e c enqueueRun
    rcases inventory.enqueue_native e c enqueueRun with ⟨_,owned⟩ | ⟨_,owned⟩
    · exact (pending.publish_return owned c b publishRun).2
    · exact (pending.publish_return owned c b publishRun).2

theorem create_tail_obligations (before : Obligations crypt tx w)
    (state : CreateOccurrences locals pid items ret w) (first : SkbId) (a b : Ambient)
    (run : ((TxDisposition.createTailSource pid items first ret).run w).run a=.ok (((),v),b)) :
    Obligations crypt tx v := by
  simp only [TxDisposition.createTailSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ok,u,c,branchRun,tail⟩:=run
  have guard:=(hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun w=>Obligations crypt tx w ∧ CreateOccurrences locals pid items ret w)
      .createDataOk (ret == 0)) w a ok u c ⟨before,state⟩ branchRun
  cases ok with
  | true=>
    simp only [ite_true] at tail
    cases tail
    exact guard.2.1
  | false=>
    have nonzero:ret≠0 := by simpa using guard.1.symm
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨pipe,t,e,branchRun,tail⟩:=tail
    have next:=(hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (fun w=>Obligations crypt tx w ∧ CreateOccurrences locals pid items ret w)
        .createDataOkEpipe (ret == -WG.EPIPE)) u c pipe t e guard.2 branchRun
    cases pipe with
    | true=>
      simp only [ite_true] at tail
      cases tail
      exact next.2.1
    | false=>
      have nonpipe:ret≠ -Leanux.EPIPE := by simpa [WG.EPIPE,Leanux.EPIPE] using next.1.symm
      have saved:TxInventory (⟨.unpublished,pid,items⟩::locals) t := by
        simpa [CreateOccurrences,nonzero,nonpipe] using next.2.2
      simp only [Bool.false_eq_true,ite_false] at tail
      exact next.2.1.cleanup saved first e b tail

theorem Obligations.create (before : Obligations crypt tx w)
    (inventory : TxInventory (⟨.unpublished,pid,items⟩::locals) w)
    (physical : TxDisposition.LiveFrontier.Physical w) (device : w.dev=some d)
    (a b : Ambient)
    (run : ((createData pid items).run w).run a=.ok (((),v),b)) : Obligations crypt tx v := by
  have factor:createData pid items=(do
      let some first:=items.head? | invariant "an empty ring item"
      let ret←createReturnSource pid items
      TxDisposition.createTailSource pid items first ret) := by
    simp only [TxDisposition.createSource_factor,createReturnSource,createPublishReturn,
      bind_assoc,bind_if_source,pure_bind]
    rfl
  rw [factor] at run
  cases head:items.head? with
  | none=>simp only [head] at run; cases run
  | some first=>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨ret,u,c,front,tail⟩:=run
    exact create_tail_obligations (before.create_return inventory physical device a c front)
      (inventory.create_return a c front) first c b tail

end Leanux.Proofs.WG.RetirementSecurity.TxWork
