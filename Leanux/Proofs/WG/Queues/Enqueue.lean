import Leanux.Proofs.WG.Keypairs.Frames.WGTransitions
import Leanux.Proofs.WG.Lifetimes.ReceiveEntry
import Leanux.Proofs.WG.Queues.PtrRing

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Original TX enqueue result refinement. Peer-queue refusal precedes the
ring-full test; queue-work failures remain errors, not ordinary return codes.
No well-formedness, ownership, or reachability premise is used. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def encryptRing (w : WGWorld) : Option (PtrRing (List SkbId)) :=
  w.dev.map (·.encryptQueue)

theorem encryptRing_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => encryptRing (project w)) a :=
  ha.of_factor (fun store : WGStoreView => store.dev.map (·.encryptQueue))
    (fun w => encryptRing (project w)) (fun _ => rfl)

theorem setPeer_encryptRing (pid : PeerId) (p : Peer) :
    SameView encryptRing (setPeer pid p) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [encryptRing, Option.map_map, Function.comp_def]

theorem getPeer_encryptRing (pid : PeerId) : SameView encryptRing (getPeer pid) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hr
  exact congrArg encryptRing (Peers.getPeer_current pid w v p ambient ambient' hr).1

/-- Exact alternatives for every ordinary return: successful production,
peer-queue refusal, or physical ring fullness. Both refusals preserve the ring. -/
def EnqueueResult (before : Option (PtrRing (List SkbId))) (item : List SkbId)
    (ret : Int) (after : Option (PtrRing (List SkbId))) : Prop :=
  (ret = 0 ∧ after = before.map (fun r => r.produce item)) ∨
  (ret = -ENOSPC ∧ after = before) ∨
  (ret = -EPIPE ∧ after = before ∧ ∃ r, before = some r ∧ r.full = true)

theorem enqueue_ring_wp (before : Option (PtrRing (List SkbId)))
    (pid : PeerId) (item : List SkbId) :
    ⦃fun w => ⌜encryptRing w = before⌝⦄ enqueuePerDeviceAndPeer pid item
    ⦃⇓? ret w => ⌜EnqueueResult before item ret (encryptRing w)⌝⦄ := by
  let P := fun w : WGWorld => encryptRing w = before
  have packet_spec (id : SkbId) :
      Preserves P (setTxSkb id (fun p => {p with state := .uncrypted})) := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [P, encryptRing, hd] using hg
  have branch_spec (d : Decision) (b : Bool) (Q : WGWorld → Prop) :
      Hoare (branch d b : WG.M Bool) Q (fun x w => x = b ∧ Q w) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hq hr
    change Except.ok ((b, w), _) = Except.ok ((x, v), ambient') at hr
    cases hr
    exact ⟨rfl, hq⟩
  have device : Hoare getDev P
      (fun d w => P w ∧ before = some d.encryptQueue) := by
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
      exact ⟨hp, hp.symm.trans (by simp [encryptRing, hd])⟩
  have edit (f : Device → Device) (hf : ∀ d, (f d).encryptQueue = d.encryptQueue) :
      SameView encryptRing (modifyDev f) := by
    apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
    simp [encryptRing, Option.map_map, Function.comp_def, hf]
  have returned (ret : Int) (Q : WGWorld → Prop)
      (hq : ∀ w, Q w → EnqueueResult before item ret (encryptRing w)) :
      Hoare (pure ret : WG.M Int) Q (fun ret w => EnqueueResult before item ret (encryptRing w)) :=
    hoare_consequence (hoare_pure ret Q) (fun _ h => h)
      (fun _ w h => h.1 ▸ hq w h.2)
  unfold enqueuePerDeviceAndPeer
  cases item.head? with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' _ hr
    cases hr
  | some first =>
    apply hoare_bind _ _ (packet_spec first)
    intro _
    apply hoare_bind _ _ ((getPeer_encryptRing pid).wp (fun r => r = before))
    intro p
    apply hoare_bind _ _ (branch_spec .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS) P)
    intro refused
    cases refused with
    | true =>
      exact returned _ _ (fun _ h => Or.inr (Or.inl ⟨rfl, h.2⟩))
    | false =>
      apply hoare_consequence ?_ (fun _ h => h.2) (fun _ _ h => h)
      apply hoare_bind _ _ ((setPeer_encryptRing pid {p with txQueue := p.txQueue.enqueue item}).wp
        (fun r => r = before))
      intro _
      apply hoare_bind _ _ device
      intro d
      let Q := fun r : Option (PtrRing (List SkbId)) => r = before ∧ before = some d.encryptQueue
      apply hoare_bind _ _ ((encryptRing_kernel
        (Lifetimes.cpumaskNextOnlineFrom_sameStore d.encryptLastCpu)).wp Q)
      intro cpu
      apply hoare_bind _ _ ((edit (fun d => {d with encryptLastCpu := cpu}) (fun _ => rfl)).wp Q)
      intro _
      apply hoare_bind _ _ (branch_spec .enqueueRingFull d.encryptQueue.full
        (fun w => Q (encryptRing w)))
      intro full
      cases full with
      | true =>
        exact returned _ _ (fun _ h => Or.inr (Or.inr
          ⟨rfl, h.2.1, d.encryptQueue, h.2.2, h.1.symm⟩))
      | false =>
        apply hoare_consequence ?_ (fun _ h => h.2) (fun _ _ h => h)
        apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker)
          (fun w => Q (encryptRing w)))
        intro _
        have produced : Hoare (modifyDev fun d => {d with encryptQueue := d.encryptQueue.produce item})
            (fun w => Q (encryptRing w))
            (fun _ w => encryptRing w = before.map (fun r => r.produce item)) := by
          apply (hoare_iff_run_ambient _ _ _).mpr
          intro w ambient x v ambient' hp hr
          cases hr
          simp only [encryptRing, Option.map_map, Function.comp_def]
          rw [← hp.1]
          simp only [encryptRing, Option.map_map, Function.comp_def]
        apply hoare_bind _ _ produced
        intro _
        exact returned 0 _ (fun _ h => Or.inl ⟨rfl, h⟩)

theorem enqueue_ring_result (pid : PeerId) (item : List SkbId)
    (w v : WGWorld) (ambient ambient' : Ambient) (ret : Int)
    (hr : ((enqueuePerDeviceAndPeer pid item).run w).run ambient = .ok ((ret, v), ambient')) :
    EnqueueResult (encryptRing w) item ret (encryptRing v) :=
  (hoare_iff_run_ambient _ _ _).mp (enqueue_ring_wp (encryptRing w) pid item)
    w ambient ret v ambient' rfl hr

theorem enqueue_epipe (pid : PeerId) (item : List SkbId) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeer pid item).run w).run ambient = .ok ((-EPIPE, v), ambient')) :
    encryptRing v = encryptRing w ∧
      ∃ r, encryptRing w = some r ∧ r.full = true := by
  have h := enqueue_ring_result pid item w v ambient ambient' (-EPIPE) hr
  simpa [EnqueueResult, EPIPE, ENOSPC] using h

end Leanux.Proofs.WG.Queues
