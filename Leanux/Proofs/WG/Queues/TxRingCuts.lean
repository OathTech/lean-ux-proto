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
    ⦃fun w => ⌜nativeCell w = before⌝⦄ enqueuePerDeviceAndPeer pid id
      ⦃⇓? ret w => ⌜EnqueueResult before id ret (nativeCell w)⌝⦄ := by
  have packet {α : Type} (a : SkbM α) :
      Hoare (liftSkb a)
        (fun w => nativeCell w = before) (fun _ w => nativeCell w = before) := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at packet
  have hp := fun pid => (getPeer_frame pid).wp (fun t => t = before)
  have hset := fun pid p => (setPeer_frame pid p).wp (fun t => t = before)
  have hc := fun cpu => (kernel (Lifetimes.cpumaskNextOnlineFrom_sameStore cpu)).wp (fun t => t = before)
  have hq : Hoare (queueDeviceWork .encryptWorker : WG.M Unit)
      (fun w => nativeCell w = before) (fun _ w => nativeCell w = before) :=
    hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker) _
  unfold Hoare at hq
  have prod (ds : Option Device) (hr : ds.map (fun d => (d.ifindex, d.encryptQueue)) = before) :
      ds.map (fun d => (d.ifindex, d.encryptQueue.produce id)) =
        before.map (fun (e, r) => (e, r.produce id)) := by
    rw [← hr]
    cases ds <;> rfl
  mvcgen [enqueuePerDeviceAndPeer, setTxSkb, packet, hp, hset, hc, hq,
    getDev, modifyDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [EnqueueResult, nativeCell, ENOSPC, EPIPE, WG.ENOSPC, WG.EPIPE,
    Option.map_map, Function.comp_def]
  all_goals first
    | (apply prod; assumption)
    | exact ⟨_, _, (by symm; assumption), (by assumption)⟩

theorem enqueue_result (pid : PeerId) (id : List SkbId) (w v : WGWorld) (ambient ambient' : Ambient) (ret : Int)
    (hr : ((enqueuePerDeviceAndPeer pid id).run w).run ambient = .ok ((ret, v), ambient')) :
    EnqueueResult (nativeCell w) id ret (nativeCell v) :=
  (hoare_iff_run_ambient _ _ _).mp (enqueue_wp (nativeCell w) pid id) w ambient ret v ambient' rfl hr

theorem enqueue_free (pid : PeerId) (id : List SkbId) (hc : nativeCell w = some (deviceIndex, r))
    (hr : ((enqueuePerDeviceAndPeer pid id).run w).run ambient = .ok ((0, v), ambient')) : r.full = false := by
  obtain ⟨s, hs, hf⟩ := enqueue_success_free pid id w v ambient ambient' hr
  have hp : encryptRing w = some r := by
    have he := congrArg (Option.map Prod.snd) hc
    simpa [nativeCell, encryptRing, Option.map_map, Function.comp_def] using he
  have he : s = r := Option.some.inj (hs.symm.trans hp)
  simpa only [he] using hf

/-- Actual consume/installation cut of encryptRingPoll, before its softirq
callback and consumed-item decision. The callback may change this ring. -/
def pollSource : WG.M (Option (List SkbId)) := do
  let (item, ring) := (← getDev).encryptQueue.consume
  modifyDev fun d => {d with encryptQueue := ring}
  return item

theorem poll_wp (deviceIndex : Nat) (r : PtrRing (List SkbId)) :
    ⦃fun w => ⌜nativeCell w = some (deviceIndex, r)⌝⦄ pollSource
    ⦃⇓? out w => ⌜out = r.consume.1 ∧ nativeCell w = some (deviceIndex, r.consume.2)⌝⦄ := by
  mvcgen [pollSource, getDev, modifyDev, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell]
  all_goals subst_vars
  all_goals simp_all [PtrRing.consume]
  all_goals split at * <;> simp_all

theorem poll_result (hc : nativeCell w = some (deviceIndex, r))
    (hr : (pollSource.run w).run ambient = .ok ((out, v), ambient')) :
    out = r.consume.1 ∧ nativeCell v = some (deviceIndex, r.consume.2) :=
  (hoare_iff_run_ambient _ _ _).mp (poll_wp deviceIndex r) w ambient out v ambient' hc hr

end Leanux.Proofs.WG.Queues.TxRing
