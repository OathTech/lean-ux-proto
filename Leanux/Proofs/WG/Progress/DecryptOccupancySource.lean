import Leanux.Proofs.WG.Progress.DecryptOccupancyFrames
import Leanux.Proofs.WG.Progress.ActivationExitSource
import Leanux.Proofs.WG.Progress.ActivationRefillFrames

/-! Actual decrypt step and iteration effects, followed by a decreasing
live-FIFO proof for the existing activation inspector. Earlier callback and
section-stop errors retain their original outcomes; no fresh observer is used. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DecryptOccupancy
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
open Leanux.Proofs.WG.Queues

theorem step_effect (deviceIndex : Nat) (r : PtrRing SkbId) :
    Hoare (decryptStep napiSoftirq napiIrqExit)
      (fun w => RxRing.cell w = some (deviceIndex,r))
      (fun value w => value = r.consume.1.isSome ∧
        RxRing.cell w = some (deviceIndex,r.consume.2)) := by
  rw [← RxRing.stepSource_eq]
  unfold RxRing.stepSource
  apply hoare_bind _ _ (RxRing.napiSoftirq_cell _)
  intro _
  have poll : Hoare (liftWG RxRing.pollSource)
      (fun w => RxRing.cell w = some (deviceIndex,r))
      (fun out w => out = r.consume.1 ∧ RxRing.cell w = some (deviceIndex,r.consume.2)) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w out v pre run
    rw [liftWG_run] at run
    cases h : (RxRing.pollSource.run w.wg).run w.ambient with
    | error e => simp [h, Except.map] at run
    | ok result =>
      obtain ⟨⟨value,g⟩,ambient⟩ := result
      simp [h] at run
      obtain ⟨rfl,rfl⟩ := run
      exact RxRing.poll_result pre h
  apply hoare_bind _ _ poll
  intro out
  cases out with
  | none =>
    apply hoare_consequence (hoare_pure false _)
      (fun _ h => h) (fun _ _ h => ⟨by rw [h.1, ← h.2.1]; rfl, h.2.2⟩)
  | some id =>
    let P := fun w : World => some id = r.consume.1 ∧
      RxRing.cell w = some (deviceIndex,r.consume.2)
    have keep {α : Type} (a : Leanux.M α) (h : SameView RxRing.cell a) : Preserves P a :=
      h.wp (fun cell => some id = r.consume.1 ∧ cell = some (deviceIndex,r.consume.2))
    have tail : Preserves P (do
        let decrypted ← decryptPacket (← getRxSkb id)
        if ← branch .decWorkerDecrypted decrypted.isSome then
          let some d := decrypted | invariant "unreachable"
          setRxSkb id fun _ => d
          enqueuePerPeerRx napiIrqExit id .crypted
        else enqueuePerPeerRx napiIrqExit id .dead
        napiSoftirq : Leanux.M Unit) := by
      apply keep
      ring_poll_source [] using [enqueue_cell, RxRing.napiSoftirq_cell]
        with [RxRing.decryptPacket_frame]
    have result := hoare_consequence (hoare_bind _ _ tail (fun _ => hoare_pure true P))
      (fun _ h => h)
      (fun (value : Bool) (w : World) h => show value = r.consume.1.isSome ∧ RxRing.cell w = some (deviceIndex,r.consume.2) from ⟨by rw [h.1, ← h.2.1]; rfl, h.2.2⟩)
    apply Eq.mp ?_ result
    congr 1
    simp only [bind_assoc]
    congr 1
    funext pkt
    congr 1
    funext decrypted
    congr 1
    funext decision
    cases decision <;> cases decrypted <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]

theorem iteration_effect (a : Activation) (worker : a.worker = .decryptWorker)
    (deviceIndex : Nat) (r : PtrRing SkbId)
    (w v : World) (value : IterResult)
    (pre : RxRing.cell w = some (deviceIndex,r))
    (run : (Activation.iter a).run w = .ok (value,v)) :
    (value = .ended ↔ r.consume.1 = none) ∧
      RxRing.cell v = some (deviceIndex,r.consume.2) := by
  simp only [Activation.iter,worker,decryptIter,workerIter,StateT.run_bind] at run
  cases step : (decryptStep napiSoftirq napiIrqExit).run w with
  | error error => simp [step] at run
  | ok result =>
    obtain ⟨item,middle⟩ := result
    have effect := (hoare_iff_run _ _ _).mp (step_effect deviceIndex r) w item middle pre step
    cases item with
    | false =>
      simp only [step] at run
      change Except.ok (.ended,middle) = Except.ok (value,v) at run
      cases run
      exact ⟨by simpa using effect.1.symm, effect.2⟩
    | true =>
      simp only [step] at run
      change ((do branch .decWorkerNeedResched (← condResched .decryptWorker) : Leanux.M Bool).run middle >>=
        fun out => .ok ((if out.1 then IterResult.yielded else .continued),out.2)) = .ok (value,v) at run
      cases ha : (do branch .decWorkerNeedResched (← condResched .decryptWorker) : Leanux.M Bool).run middle with
      | error error => simp [ha] at run
      | ok result =>
        obtain ⟨yielded,final⟩ := result
        have preserved := (ProjectedAction.iff_run _ _ _).mp afterItem_cell middle yielded final ha
        cases yielded <;> simp only [ha] at run
        all_goals cases run
        all_goals refine ⟨?_, preserved.trans effect.2⟩
        all_goals
          constructor
          · intro impossible; cases impossible
          · intro absent; rw [absent] at effect; cases effect.1

theorem iteration_rep (a : Activation) (worker : a.worker = .decryptWorker)
    (deviceIndex capacity batch : Nat) (live : List SkbId)
    (w v : World) (value : IterResult)
    (pre : Rep deviceIndex capacity batch live (Campaign2.Product.snapshot w))
    (run : (Activation.iter a).run w = .ok (value,v)) :
    (value = .ended ↔ live = []) ∧
      Rep deviceIndex capacity batch live.tail (Campaign2.Product.snapshot v) := by
  obtain ⟨tail,stale,bounds,present⟩ := pre
  have effect := iteration_effect a worker deviceIndex _ w v value present run
  obtain ⟨tail',stale',bounds',consume⟩ := Ring.consume_preserves (batch:=batch) bounds
  rw [consume] at effect
  refine ⟨?_,tail',stale',bounds',effect.2⟩
  simpa using effect.1

theorem loop_no_exhaustion (original : Activation) (occupancy refills fuel count : Nat)
    (active : Activation) (entry : World) (worker : active.worker = .decryptWorker)
    (deviceIndex capacity batch : Nat) (live : List SkbId)
    (pre : Rep deviceIndex capacity batch live (Campaign2.Product.snapshot entry))
    (enough : live.length < fuel) :
    match activationExitLoop original occupancy refills fuel count active entry with
    | .exhausted .. => False
    | _ => True := by
  induction fuel generalizing count active entry live with
  | zero => simp at enough
  | succ fuel ih =>
    unfold activationExitLoop
    cases run : (Activation.iter active).run entry with
    | error error => trivial
    | ok result =>
      obtain ⟨value,after⟩ := result
      have rank := iteration_rep active worker deviceIndex capacity batch live entry after value pre run
      cases value with
      | ended => trivial
      | yielded => trivial
      | continued =>
        have nonempty : live ≠ [] := fun empty => IterResult.noConfusion (rank.1.mpr empty)
        exact ih (count+1) _ after worker live.tail rank.2
          (by cases live <;> simp_all)

theorem activation_no_exhaustion (a : Activation) (worker : a.worker = .decryptWorker)
    (deviceIndex capacity batch : Nat) (live : List SkbId) (entry : World)
    (pre : Rep deviceIndex capacity batch live (Campaign2.Product.snapshot entry)) :
    NoExhaustion ((activationExitRun a entry).map Campaign2.Product.snapshot) := by
  obtain ⟨tail,stale,bounds,present⟩ := pre
  have cellEq : RxRing.cell entry = some (deviceIndex,Ring.ringOf capacity batch tail stale live) := present
  obtain ⟨d,device,fields⟩ : ∃ d,entry.wg.dev=some d ∧ d.ifindex=deviceIndex ∧
      d.decryptQueue=Ring.ringOf capacity batch tail stale live := by
    cases hd : entry.wg.dev with
    | none => simp [RxRing.cell,hd] at cellEq
    | some d => exact ⟨d,rfl,by simpa [RxRing.cell,hd] using cellEq⟩
  have occupancy : (Activation.occupancy a).run entry = .ok (live.length,entry) := by
    have read : (liftWG getDev).run entry = .ok (d,entry) := by
      rw [liftWG_run]
      simp [getDev,device]
      rfl
    simp only [Activation.occupancy,worker]
    change ((liftWG getDev).run entry >>= fun out => .ok (out.1.decryptQueue.count,out.2)) = _
    rw [read]
    change Except.ok (d.decryptQueue.count,entry) = _
    rw [fields.2,Ring.count bounds]
  let refills := (entry.ambient.hidden.map List.length).getD 0 +
    d.peers.toList.countP (·.2.napiScheduled) * WG.NAPI_POLL_WEIGHT
  have refill := RecordSuffix.activationRefills_run entry d device
  change Activation.refills.run entry = .ok (refills,entry) at refill
  unfold activationExitRun
  rw [occupancy]
  dsimp only
  rw [refill]
  have h := loop_no_exhaustion a live.length refills (live.length+refills+1) 0 a entry worker
    deviceIndex capacity batch live ⟨tail,stale,bounds,present⟩ (by omega)
  cases result : activationExitLoop a live.length refills (live.length+refills+1) 0 a entry <;>
    simp [ActivationExitAudit.map,ActivationExitResult.map,NoExhaustion,result] at h ⊢


end Leanux.Proofs.WG.Progress.DecryptOccupancy
