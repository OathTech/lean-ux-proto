import Leanux.Proofs.WG.Progress.BatchDrainModel
import Leanux.Proofs.WG.Progress.BatchDrainFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Exact all-outcome factor on recorded entries. The loop, completion refusal
and delivery errors remain those of the original source. -/
theorem afterBatch_recorded_source (entry : World)
    (recorded : entry.ambient.hidden.isSome = true) :
    afterBatch.run entry = afterBatchRecorded.run entry := by
  unfold afterBatch afterBatchRecorded afterBatchRecordedLoop afterBatchDrainSuffix
  simp only [bind_assoc, pure_bind]
  dsimp only [StateT.run, StateT.bind, StateT.pure, modifyWG, getAmbient,
    monadLift, MonadLift.monadLift, liftM, liftWG, liftAmbient, modify, modifyGet, get, getThe,
    MonadStateOf.get, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet,
    Bind.bind, Pure.pure, Except.bind, Except.pure]
  cases records : entry.ambient.hidden with
  | none => simp [records] at recorded
  | some rs => rfl

theorem afterBatchDrainSuffix_drained :
    Campaign2.Product.Ensures afterBatchDrainSuffix (fun _ => True)
      (fun _ s => BatchDrained s) := by
  intro entry result final _ run
  cases device : entry.wg.dev with
  | none =>
    have absent : (liftWG getDev).run entry =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      dsimp only [liftWG, getDev, StateT.run, StateT.bind, get, getThe,
        MonadStateOf.get, StateT.get, Bind.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
      rw [device]
      rfl
    change ((liftWG getDev).run entry >>= _) = _ at run
    rw [absent] at run
    cases run
  | some d =>
    have read : (liftWG getDev).run entry = .ok (d, entry) := by
      dsimp only [liftWG, getDev, StateT.run, StateT.bind, get, getThe,
        MonadStateOf.get, StateT.get, Bind.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
      rw [device]
      rfl
    change ((liftWG getDev).run entry >>= fun (d, middle) =>
      ((do
        requireDrained "the batch queued"
          [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
           !d.handshakeQueue.empty, d.handshakeQueueLen != 0]
        deliverSent : Leanux.M Unit).run middle)) = _ at run
    rw [read] at run
    dsimp only [Except.bind] at run
    let checks : List Bool := [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty,
      !d.sendWorkQueue.isEmpty, !d.handshakeQueue.empty, d.handshakeQueueLen != 0]
    have flags : checks.any id = false := by
      cases flag : checks.any id with
      | false => rfl
      | true =>
        change (do requireDrained "the batch queued" checks; deliverSent : Leanux.M Unit).run entry = _ at run
        unfold requireDrained at run
        rw [flag] at run
        change Except.error _ = Except.ok _ at run
        cases run
    let pending := entry.ambient.pendingWork.filterMap fun i => Worker.all.find? (·.index == i)
    have pendingRead : (Leanux.pendingDeviceUnits : Leanux.M (List Worker)).run entry =
        .ok (pending, entry) := rfl
    have pendingEmpty : pending = [] := by
      cases hp : pending with
      | nil => rfl
      | cons worker rest =>
        change (do requireDrained "the batch queued" checks; deliverSent : Leanux.M Unit).run entry = _ at run
        unfold requireDrained at run
        rw [flags] at run
        simp only [Bool.false_eq_true, ite_false, bind_assoc] at run
        simp only [StateT.run_bind, pendingRead, hp] at run
        change Except.error _ = Except.ok _ at run
        cases run
    have napi : d.peers.toList.any (·.2.napiScheduled) = false := by
      cases scheduled : d.peers.toList.any (·.2.napiScheduled) with
      | false => rfl
      | true =>
        change (do requireDrained "the batch queued" checks; deliverSent : Leanux.M Unit).run entry = _ at run
        unfold requireDrained at run
        rw [flags] at run
        simp only [Bool.false_eq_true, ite_false, bind_assoc] at run
        simp only [StateT.run_bind, pendingRead, pendingEmpty] at run
        dsimp only [Bind.bind, Except.bind] at run
        change (((liftWG getDev).run entry >>= fun (dv, current) =>
          ((if dv.peers.toList.any (·.2.napiScheduled) then
            invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)"
            else pure ()) : Leanux.M Unit).run current) >>= fun out => deliverSent.run out.2) = _ at run
        rw [read] at run
        change ((if d.peers.toList.any (·.2.napiScheduled) then
          invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)"
          else pure ()) >>= fun _ => deliverSent : Leanux.M Unit).run entry = _ at run
        rw [scheduled] at run
        change Except.error _ = Except.ok _ at run
        cases run
    have delivery : deliverSent.run entry = .ok (result, final) := by
      change (do requireDrained "the batch queued" checks; deliverSent : Leanux.M Unit).run entry = _ at run
      unfold requireDrained at run
      rw [flags] at run
      simp only [Bool.false_eq_true, ite_false, bind_assoc] at run
      simp only [StateT.run_bind, pendingRead, pendingEmpty] at run
      dsimp only [Bind.bind, Except.bind] at run
      change (((liftWG getDev).run entry >>= fun (dv, current) =>
        ((if dv.peers.toList.any (·.2.napiScheduled) then
          invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)"
          else pure ()) : Leanux.M Unit).run current) >>= fun out => deliverSent.run out.2) = _ at run
      rw [read] at run
      change ((if d.peers.toList.any (·.2.napiScheduled) then
        invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)"
        else pure ()) >>= fun _ => deliverSent : Leanux.M Unit).run entry = _ at run
      simpa only [napi, Bool.false_eq_true, ite_false, pure_bind] using run
    have same := deliverSent_sameKernel_device_variant (some d) entry result final device delivery
    refine ⟨d, same, ?_⟩
    have queues : d.decryptQueue.empty = true ∧ d.encryptQueue.empty = true ∧
        d.txWorkQueue.isEmpty = true ∧ d.sendWorkQueue.isEmpty = true ∧
        d.handshakeQueue.empty = true ∧ d.handshakeQueueLen = 0 := by
      simpa [checks, Bool.or_eq_false_iff] using flags
    exact ⟨queues.1, queues.2.1, queues.2.2.1, queues.2.2.2.1,
      queues.2.2.2.2.1, queues.2.2.2.2.2, napi⟩

end Leanux.Proofs.WG.Progress
