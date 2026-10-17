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
  let P := fun w : WGWorld => nativeCell w = before
  have packet_spec (id : SkbId) :
      Preserves P (setRxSkb id (fun p => {p with state := .uncrypted})) := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [P, nativeCell, hd] using hg
  have branch_spec (d : Decision) (b : Bool) (Q : WGWorld → Prop) :
      Hoare (branch d b : WG.M Bool) Q (fun x w => x = b ∧ Q w) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hq hr
    change Except.ok ((b, w), _) = Except.ok ((x, v), ambient') at hr
    cases hr
    exact ⟨rfl, hq⟩
  have device : Hoare getDev P
      (fun d w => P w ∧ before = some (d.ifindex, d.decryptQueue)) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hp hr
    cases hd : w.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      have he : (getDev.run w).run ambient = .ok ((old, w), ambient) := by
        simp [getDev, hd] <;> rfl
      rw [he] at hr
      cases hr
      exact ⟨hp, hp.symm.trans (by simp [nativeCell, hd])⟩
  have edit (cpu : Int) :
      SameView nativeCell (modifyDev fun d => {d with decryptLastCpu := cpu}) := by
    apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
    simp [nativeCell, Option.map_map, Function.comp_def]
  have returned (ret : Int) (Q : WGWorld → Prop)
      (hq : ∀ w, Q w → EnqueueResult before id ret (nativeCell w)) :
      Hoare (pure ret : WG.M Int) Q (fun ret w => EnqueueResult before id ret (nativeCell w)) :=
    hoare_consequence (hoare_pure ret Q) (fun _ h => h)
      (fun _ w h => h.1 ▸ hq w h.2)
  have read_spec : Preserves P (getRxSkb id) := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [P, nativeCell, hd] using hg
  unfold enqueuePerDeviceAndPeerRx
  apply hoare_bind _ _ (packet_spec id)
  intro _
  apply hoare_bind _ _ read_spec
  intro pkt
  apply hoare_bind _ _ ((getPeer_frame pkt.peer).wp (fun r => r = before))
  intro p
  apply hoare_bind _ _ (branch_spec .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS) P)
  intro refused
  cases refused with
  | true =>
    exact returned _ _ (fun _ h => Or.inr (Or.inl ⟨rfl, h.2⟩))
  | false =>
    apply hoare_consequence ?_ (fun _ h => h.2) (fun _ _ h => h)
    apply hoare_bind _ _ ((setPeer_frame pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).wp
      (fun r => r = before))
    intro _
    apply hoare_bind _ _ device
    intro d
    let Q := fun r : Option (Nat × PtrRing (SkbId)) => r = before ∧ before = some (d.ifindex, d.decryptQueue)
    apply hoare_bind _ _ ((kernel
      (Lifetimes.cpumaskNextOnlineFrom_sameStore d.decryptLastCpu)).wp Q)
    intro cpu
    apply hoare_bind _ _ ((edit cpu).wp Q)
    intro _
    apply hoare_bind _ _ (branch_spec .enqueueRingFull d.decryptQueue.full
      (fun w => Q (nativeCell w)))
    intro full
    cases full with
    | true =>
      exact returned _ _ (fun _ h => Or.inr (Or.inr
        ⟨rfl, h.2.1, d.ifindex, d.decryptQueue, h.2.2, h.1.symm⟩))
    | false =>
      apply hoare_consequence ?_ (fun _ h => h.2) (fun _ _ h => h)
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.queueDeviceWork .decryptWorker)
        (fun w => Q (nativeCell w)))
      intro _
      have produced : Hoare (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id})
          (fun w => Q (nativeCell w))
          (fun _ w => nativeCell w = before.map (fun (e, r) => (e, r.produce id))) := by
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w ambient x v ambient' hp hr
        cases hr
        simp only [nativeCell, Option.map_map, Function.comp_def]
        rw [← hp.1]
        simp only [nativeCell, Option.map_map, Function.comp_def]
      apply hoare_bind _ _ produced
      intro _
      exact returned 0 _ (fun _ h => Or.inl ⟨rfl, h⟩)

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
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient out v ambient' hc hr
  cases hd : w.dev with
  | none =>
    simp [pollSource, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    have cell : d.ifindex = deviceIndex ∧ d.decryptQueue = r := by
      simpa [nativeCell, hd] using hc
    cases hp : d.decryptQueue.peek with
    | none =>
      simp [pollSource, getDev, hd, PtrRing.consume, hp, branch, AmbientM.branch] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [nativeCell, hd, ← cell.2, ← cell.1, PtrRing.consume, hp]
    | some id =>
      simp [pollSource, getDev, hd, PtrRing.consume, hp, branch, AmbientM.branch, modifyDev] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [nativeCell, ← cell.2, ← cell.1, PtrRing.consume, hp]

theorem poll_result (hc : nativeCell w = some (deviceIndex, r))
    (hr : (pollSource.run w).run ambient = .ok ((out, v), ambient')) :
    out = r.consume.1 ∧ nativeCell v = some (deviceIndex, r.consume.2) :=
  (hoare_iff_run_ambient _ _ _).mp (poll_wp deviceIndex r) w ambient out v ambient' hc hr

end Leanux.Proofs.WG.Queues.RxRing
