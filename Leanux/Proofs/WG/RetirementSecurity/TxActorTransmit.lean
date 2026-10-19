import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionCompletion
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageCoherent

/-! Native TX iteration transport derives both packet coverage and actor
retention from the actual step. Only the scheduler's surrounding crypt-ahead
and other worker families remain separate caller obligations. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

abbrev Covered (locals : List TxLocalBatch) (crypt : List (List SkbId)) := TxCovered.Inv locals crypt

theorem reschedule (worker : Worker) :
    SameView (fun w : World=>(w.wg,w.ambient.suspended)) (Env.condResched worker) := by
  intro initial
  let P := fun w : World=>(w.wg,w.ambient.suspended)=initial
  have peek : Preserves P (peekHiddenSite : Leanux.M (Option Nat)) :=
    TxActorFrames.lift_ambient TxActorFrames.peek_site initial
  have read (site : HiddenSite) : Preserves P (hidden site : Leanux.M (List UInt8)) :=
    TxActorFrames.hidden_product site initial
  have stopped {α : Type} (message : String) : Preserves P (invariant message : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
  change Preserves P _
  routing_tx_source [Env.condResched] using [peek,read,stopped]

theorem transmit_step (before : At (Covered locals crypt) crypt [pid] w)
    (run : (liftWG (txStep pid)).run w=.ok (result,v)) :
    At (Covered locals crypt) crypt (if result then [pid] else []) v := by
  have native:=HolderPoll.native_receipt run
  have same:=TxSuspension.native (TxSuspension.tx_step pid) native
  have after:Covered locals crypt v.wg :=
    (hoare_iff_run_ambient _ _ _).mp
      (TxCovered.join (OccurrenceTx.step pid) (TxCoverageWorkers.step pid))
      w.wg w.ambient result v.wg v.ambient before.2 native
  have inv:TxInventory locals w.wg := before.2.1.2.1
  cases result with
  | false=>
    have service:=before.1.end_actor inv w.ambient v.ambient native
    change Obligations crypt (actors w.ambient.suspended) v.wg at service
    refine ⟨?_,after⟩
    change Obligations crypt (actors v.ambient.suspended) v.wg
    rw [same]
    exact service
  | true=>
    have service:=before.1.step inv (by simp) w.ambient v.ambient native
    exact ⟨by simpa only [ite_true,same] using service,after⟩

theorem transmit_iteration (before : At (Covered locals crypt) crypt [pid] w)
    (run : (txIter pid (Env.condResched .txWorker)).run w=.ok (result,v)) :
    At (Covered locals crypt) crypt (if result=.ended then [] else [pid]) v := by
  unfold txIter workerIter at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨processed,u,step,tail⟩:=run
  have service:=transmit_step before step
  cases processed with
  | false=>cases tail; exact service
  | true=>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    rw [bind_assoc] at tail
    change ((do let needed←Env.condResched Worker.txWorker
                let value←branch Decision.txNeedResched needed
                pure (if value then IterResult.yielded else IterResult.continued) : Leanux.M IterResult).run u)=
      .ok (result,v) at tail
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨needed,t,rescheduled,tail⟩:=tail
    have same: (t.wg,t.ambient.suspended)=(u.wg,u.ambient.suspended) :=
      (ProjectedAction.iff_run _ _ _).mp (reschedule .txWorker) u needed t rescheduled
    have next:=service.frame same
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨flag,z,branched,returned⟩:=tail
    cases branched
    cases needed <;> cases returned <;> exact next

end Leanux.Proofs.WG.RetirementSecurity.TxWork
