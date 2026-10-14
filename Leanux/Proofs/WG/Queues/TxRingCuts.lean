import Leanux.Proofs.WG.Queues.TxRingFrames

/-! Original enqueue endpoints and the exact consume/installation source cut.
No endpoint behavior is supplied as a premise. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def EnqueueResult (before : Option (Nat × PtrRing (List SkbId))) (id : List SkbId)
    (ret : Int) (after : Option (Nat × PtrRing (List SkbId))) : Prop :=
  (ret = 0 ∧ after = before.map (fun (e, r) => (e, r.produce id))) ∨
  (ret = -ENOSPC ∧ after = before) ∨
  (ret = -EPIPE ∧ after = before ∧ ∃ e r, before = some (e, r) ∧ r.full = true)

theorem enqueue_wp (before : Option (Nat × PtrRing (List SkbId))) (pid : PeerId) (id : List SkbId) :
    ⦃fun w => ⌜cell w = before⌝⦄ enqueuePerDeviceAndPeer pid id
      ⦃⇓? ret w => ⌜EnqueueResult before id ret (cell w)⌝⦄ := by
  have hs := fun first => (setTx_frame first (fun p => {p with state := .uncrypted})).wp (fun t => t = before)
  have hp := fun pid => (getPeer_frame pid).wp (fun t => t = before)
  have hset := fun pid p => (setPeer_frame pid p).wp (fun t => t = before)
  have hc := fun cpu => (kernel (Lifetimes.cpumaskNextOnlineFrom_sameKernel cpu)).wp (fun t => t = before)
  have hq := (kernel (Lifetimes.queueDeviceWork_sameKernel .encryptWorker)).wp (fun t => t = before)
  have prod (ds : Option Device) (hr : ds.map (fun d => (d.ifindex, d.encryptQueue)) = before) :
      ds.map (fun d => (d.ifindex, d.encryptQueue.produce id)) =
        before.map (fun (e, r) => (e, r.produce id)) := by
    rw [← hr]
    cases ds <;> rfl
  mvcgen [enqueuePerDeviceAndPeer, hs, hp, hset, hc, hq,
    getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [EnqueueResult, cell, ENOSPC, EPIPE, WG.ENOSPC, WG.EPIPE,
    Option.map_map, Function.comp_def]
  all_goals first
    | (apply prod; assumption)
    | exact ⟨_, _, (by symm; assumption), (by assumption)⟩

theorem enqueue_result (pid : PeerId) (id : List SkbId) (w v : World) (ret : Int)
    (hr : (enqueuePerDeviceAndPeer pid id).run w = .ok (ret, v)) :
    EnqueueResult (cell w) id ret (cell v) :=
  (hoare_iff_triple _ _ _).mpr (enqueue_wp (cell w) pid id) w ret v rfl hr

theorem enqueue_free (pid : PeerId) (id : List SkbId) (hc : cell w = some (deviceIndex, r))
    (hr : (enqueuePerDeviceAndPeer pid id).run w = .ok (0, v)) : r.full = false := by
  obtain ⟨s, hs, hf⟩ := enqueue_success_free pid id w v hr
  have hp : encryptRing w = some r := by
    have he := congrArg (Option.map Prod.snd) hc
    simpa [cell, encryptRing, Option.map_map, Function.comp_def] using he
  have he : s = r := Option.some.inj (hs.symm.trans hp)
  simpa only [he] using hf

/-- Original encryptStep prefix after softirq: branch, then installation.
Returning the consumed id is proof-side factoring, not an extra source read. -/
def pollSource : M (Option (List SkbId)) := do
  match (← getDev).encryptQueue.consume with
  | (none, _) =>
    _ ← branch .encWorkerConsumed false
    return none
  | (some id, ring) =>
    _ ← branch .encWorkerConsumed true
    modifyDev fun d => {d with encryptQueue := ring}
    return some id

theorem poll_wp (deviceIndex : Nat) (r : PtrRing (List SkbId)) :
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

end Leanux.Proofs.WG.Queues.TxRing
