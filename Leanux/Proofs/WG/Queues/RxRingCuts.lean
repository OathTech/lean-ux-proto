import Leanux.Proofs.WG.Queues.RxRingFrames

/-! Original enqueue endpoints and the exact consume/installation source cut.
No endpoint behavior is supplied as a premise. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def EnqueueResult (before : Option (Nat × PtrRing SkbId)) (id : SkbId)
    (ret : Int) (after : Option (Nat × PtrRing SkbId)) : Prop :=
  (ret = 0 ∧ after = before.map (fun (e, r) => (e, r.produce id))) ∨
  (ret = -ENOSPC ∧ after = before) ∨
  (ret = -EPIPE ∧ after = before ∧ ∃ e r, before = some (e, r) ∧ r.full = true)

theorem enqueue_wp (before : Option (Nat × PtrRing SkbId)) (id : SkbId) :
    ⦃fun w => ⌜cell w = before⌝⦄ enqueuePerDeviceAndPeerRx id
      ⦃⇓? ret w => ⌜EnqueueResult before id ret (cell w)⌝⦄ := by
  have hs := (setRx_frame id (fun p => {p with state := .uncrypted})).wp (fun t => t = before)
  have hg := (getRx_frame id).wp (fun t => t = before)
  have hp := fun pid => (getPeer_frame pid).wp (fun t => t = before)
  have hset := fun pid p => (setPeer_frame pid p).wp (fun t => t = before)
  have hc := fun cpu => (kernel (Lifetimes.cpumaskNextOnlineFrom_sameKernel cpu)).wp (fun t => t = before)
  have hq := (kernel (Lifetimes.queueDeviceWork_sameKernel .decryptWorker)).wp (fun t => t = before)
  have prod (ds : Option Device) (hr : ds.map (fun d => (d.ifindex, d.decryptQueue)) = before) :
      ds.map (fun d => (d.ifindex, d.decryptQueue.produce id)) =
        before.map (fun (e, r) => (e, r.produce id)) := by
    rw [← hr]
    cases ds <;> rfl
  mvcgen [enqueuePerDeviceAndPeerRx, hs, hg, hp, hset, hc, hq,
    getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [EnqueueResult, cell, ENOSPC, EPIPE, WG.ENOSPC, WG.EPIPE,
    Option.map_map, Function.comp_def]
  all_goals first
    | (apply prod; assumption)
    | exact ⟨_, _, (by symm; assumption), (by assumption)⟩

theorem enqueue_result (id : SkbId) (w v : World) (ret : Int)
    (hr : (enqueuePerDeviceAndPeerRx id).run w = .ok (ret, v)) :
    EnqueueResult (cell w) id ret (cell v) :=
  (hoare_iff_triple _ _ _).mpr (enqueue_wp (cell w) id) w ret v rfl hr

theorem enqueue_free (id : SkbId) (hc : cell w = some (deviceIndex, r))
    (hr : (enqueuePerDeviceAndPeerRx id).run w = .ok (0, v)) : r.full = false := by
  obtain ⟨s, hs, hf⟩ := enqueue_rx_success_free id w v hr
  have hp : decryptRing w = some r := by
    have he := congrArg (Option.map Prod.snd) hc
    simpa [cell, decryptRing, Option.map_map, Function.comp_def] using he
  have he : s = r := Option.some.inj (hs.symm.trans hp)
  simpa only [he] using hf

/-- Original decryptStep prefix after softirq: branch, then installation.
Returning the consumed id is proof-side factoring, not an extra source read. -/
def pollSource : M (Option SkbId) := do
  match (← getDev).decryptQueue.consume with
  | (none, _) =>
    _ ← branch .decWorkerConsumed false
    return none
  | (some id, ring) =>
    _ ← branch .decWorkerConsumed true
    modifyDev fun d => {d with decryptQueue := ring}
    return some id

theorem poll_wp (deviceIndex : Nat) (r : PtrRing SkbId) :
    ⦃fun w => ⌜cell w = some (deviceIndex, r)⌝⦄ pollSource
    ⦃⇓? out w => ⌜out = r.consume.1 ∧ cell w = some (deviceIndex, r.consume.2)⌝⦄ := by
  mvcgen [pollSource, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all [PtrRing.consume]
  all_goals split at * <;> simp_all

theorem poll_result (hc : cell w = some (deviceIndex, r))
    (hr : pollSource.run w = .ok (out, v)) :
    out = r.consume.1 ∧ cell v = some (deviceIndex, r.consume.2) :=
  (hoare_iff_triple _ _ _).mpr (poll_wp deviceIndex r) w out v hc hr

end Leanux.Proofs.WG.Queues.RxRing
