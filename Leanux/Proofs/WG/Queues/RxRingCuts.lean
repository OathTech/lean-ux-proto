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
    ⦃fun w => ⌜nativeCell w = before⌝⦄ enqueuePerDeviceAndPeerRx id
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
  have hq : Hoare (queueDeviceWork .decryptWorker : WG.M Unit)
      (fun w => nativeCell w = before) (fun _ w => nativeCell w = before) :=
    hoare_liftAmbient (AmbientM.queueDeviceWork .decryptWorker) _
  unfold Hoare at hq
  have prod (ds : Option Device) (hr : ds.map (fun d => (d.ifindex, d.decryptQueue)) = before) :
      ds.map (fun d => (d.ifindex, d.decryptQueue.produce id)) =
        before.map (fun (e, r) => (e, r.produce id)) := by
    rw [← hr]
    cases ds <;> rfl
  mvcgen [enqueuePerDeviceAndPeerRx, getRxSkb, setRxSkb, packet, hp, hset, hc, hq,
    getDev, modifyDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [EnqueueResult, nativeCell, ENOSPC, EPIPE, WG.ENOSPC, WG.EPIPE,
    Option.map_map, Function.comp_def]
  all_goals first
    | (apply prod; assumption)
    | exact ⟨_, _, (by symm; assumption), (by assumption)⟩

theorem enqueue_result (id : SkbId) (w v : WGWorld) (ambient ambient' : Ambient) (ret : Int)
    (hr : ((enqueuePerDeviceAndPeerRx id).run w).run ambient = .ok ((ret, v), ambient')) :
    EnqueueResult (nativeCell w) id ret (nativeCell v) :=
  (hoare_iff_run_ambient _ _ _).mp (enqueue_wp (nativeCell w) id) w ambient ret v ambient' rfl hr

theorem enqueue_free (id : SkbId) (hc : nativeCell w = some (deviceIndex, r))
    (hr : ((enqueuePerDeviceAndPeerRx id).run w).run ambient = .ok ((0, v), ambient')) : r.full = false := by
  obtain ⟨s, hs, hf⟩ := enqueue_rx_success_free id w v ambient ambient' hr
  have hp : decryptRing w = some r := by
    have he := congrArg (Option.map Prod.snd) hc
    simpa [nativeCell, decryptRing, Option.map_map, Function.comp_def] using he
  have he : s = r := Option.some.inj (hs.symm.trans hp)
  simpa only [he] using hf

/-- Original decryptStep prefix after softirq: branch, then installation.
Returning the consumed id is proof-side factoring, not an extra source read. -/
def pollSource : WG.M (Option SkbId) := do
  match (← getDev).decryptQueue.consume with
  | (none, _) =>
    _ ← branch .decWorkerConsumed false
    return none
  | (some id, ring) =>
    _ ← branch .decWorkerConsumed true
    modifyDev fun d => {d with decryptQueue := ring}
    return some id

theorem poll_wp (deviceIndex : Nat) (r : PtrRing SkbId) :
    ⦃fun w => ⌜nativeCell w = some (deviceIndex, r)⌝⦄ pollSource
    ⦃⇓? out w => ⌜out = r.consume.1 ∧ nativeCell w = some (deviceIndex, r.consume.2)⌝⦄ := by
  mvcgen [pollSource, getDev, modifyDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell]
  all_goals subst_vars
  all_goals simp_all [PtrRing.consume]
  all_goals split at * <;> simp_all

theorem poll_result (hc : nativeCell w = some (deviceIndex, r))
    (hr : (pollSource.run w).run ambient = .ok ((out, v), ambient')) :
    out = r.consume.1 ∧ nativeCell v = some (deviceIndex, r.consume.2) :=
  (hoare_iff_run_ambient _ _ _).mp (poll_wp deviceIndex r) w ambient out v ambient' hc hr

end Leanux.Proofs.WG.Queues.RxRing
