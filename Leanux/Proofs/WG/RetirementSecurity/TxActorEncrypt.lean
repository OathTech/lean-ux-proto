import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionEncrypt

/-! Native encrypt service transfers the actual polled alias through its
callback and consumes it only at terminal publication. NAPI's service contract
is explicit here, pending its concrete staging/RX caller discharge. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem encrypt_poll (before : At (Covered locals crypt) crypt tx w)
    (run : (liftWG TxRing.pollSource).run w=.ok (item,v)) :
    At (Covered locals (item.toList++crypt)) (item.toList++crypt) tx v := by
  have native:=HolderPoll.native_receipt run
  have same:=TxSuspension.native TxSuspension.poll native
  have service:=before.1.poll before.2.1.2.2.physical w.ambient v.ambient native
  refine ⟨by simpa only [same] using service,?_,?_⟩
  · exact OccurrenceEncrypt.poll before.2.1 w.ambient v.ambient native
  · exact (hoare_iff_run_ambient _ _ _).mp TxCoverageEncrypt.poll
      w.wg w.ambient item v.wg v.ambient before.2.2 native

theorem encrypt_step_service
    (before : At (Covered locals (item.toList++crypt)) (item.toList++crypt) tx w)
    (run : (RxWorkers.encryptStepTailSource item).run w=.ok (result,v)) :
    At (fun _=>True) crypt tx v := by
  have service:=before.1.encrypt_tail before.2.1.2.1 run
  have same:v.ambient.suspended=w.ambient.suspended :=
    (ProjectedAction.iff_run _ _ _).mp (TxSuspension.encryption_tail item) w result v run
  exact ⟨by simpa only [same] using service,True.intro⟩

theorem encrypt_tail_service
    (before : At (Covered locals (item.toList++crypt)) (item.toList++crypt) tx w)
    (run : (RxWorkers.encryptTailSource item).run w=.ok (result,v)) :
    At (Covered locals crypt) crypt tx v := by
  have covered:Covered locals crypt v.wg :=
    ⟨OccurrenceEncrypt.tail before.2.1 run,
      (hoare_iff_run _ _ _).mp (TxCoverageEncrypt.tail item) w result v before.2.2 run⟩
  suffices service:At (fun _=>True) crypt tx v from ⟨service.1,covered⟩
  unfold RxWorkers.encryptTailSource workerIter at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨processed,u,step,tail⟩:=run
  have service:=encrypt_step_service before step
  cases processed with
  | false=>cases tail; exact service
  | true=>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    rw [bind_assoc] at tail
    change ((do let needed←Env.condResched Worker.encryptWorker
                let value←branch Decision.encWorkerNeedResched needed
                pure (if value then IterResult.yielded else IterResult.continued) : Leanux.M IterResult).run u)=
      .ok (result,v) at tail
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨needed,t,rescheduled,tail⟩:=tail
    have same: (t.wg,t.ambient.suspended)=(u.wg,u.ambient.suspended) :=
      (ProjectedAction.iff_run _ _ _).mp (reschedule .encryptWorker) u needed t rescheduled
    have next:=service.frame same
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨flag,z,branched,returned⟩:=tail
    cases branched
    cases needed <;> cases returned <;> exact next

theorem encrypt_iteration_service
    (callback : ∀item : Option (List SkbId),Preserves
      (At (Covered locals (item.toList++crypt)) (item.toList++crypt) tx) Env.napiSoftirq)
    (before : At (Covered locals crypt) crypt tx w)
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)).run w=
      .ok (result,v)) : At (Covered locals crypt) crypt tx v := by
  rw [RxWorkers.encrypt_source,MaterialOrigin.bind_ok] at run
  obtain ⟨item,u,polled,tail⟩:=run
  have selected:=encrypt_poll before polled
  rw [MaterialOrigin.bind_ok] at tail
  obtain ⟨_,t,received,tail⟩:=tail
  have held:=(hoare_iff_run _ _ _).mp (callback item) u () t selected received
  exact encrypt_tail_service held tail

end Leanux.Proofs.WG.RetirementSecurity.TxWork
