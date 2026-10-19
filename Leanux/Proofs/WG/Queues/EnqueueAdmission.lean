import Leanux.Proofs.WG.Queues.Enqueue

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Admission guards derived independently from the original enqueue bodies.
The older EnqueueResult API is unchanged. These normal-return implications do
not count a passed guard followed by a queue-work Stop as an admission event. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def FreeEntry (before : Option (PtrRing α)) : Prop :=
  ∃ r, before = some r ∧ r.full = false

theorem enqueue_free_wp (before : Option (PtrRing (List SkbId)))
    (pid : PeerId) (item : List SkbId) :
    ⦃fun w => ⌜encryptRing w = before⌝⦄ enqueuePerDeviceAndPeer pid item
    ⦃⇓? ret _ => ⌜ret = 0 → FreeEntry before⌝⦄ := by
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
  have constant {α : Type} (a : WG.M α) (R : Prop) :
      Preserves (fun _ : WGWorld => R) a := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' h _
    exact h
  have returned (ret : Int) (Q : WGWorld → Prop)
      (hq : ∀ w, Q w → ret = 0 → FreeEntry before) :
      Hoare (pure ret : WG.M Int) Q (fun ret _ => ret = 0 → FreeEntry before) :=
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
    | true => exact returned _ _ (by intro _ _ he; cases he)
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
      | true => exact returned _ _ (by intro _ _ he; cases he)
      | false =>
        exact hoare_consequence (constant _ (FreeEntry before))
          (fun _ h => ⟨d.encryptQueue, h.2.2, h.1.symm⟩)
          (fun _ _ h _ => h)

theorem enqueue_success_free (pid : PeerId) (item : List SkbId) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeer pid item).run w).run ambient = .ok ((0, v), ambient')) :
    FreeEntry (encryptRing w) :=
  (hoare_iff_run_ambient _ _ _).mp (enqueue_free_wp (encryptRing w) pid item) w ambient 0 v ambient' rfl hr rfl

def decryptRing (w : WGWorld) : Option (PtrRing SkbId) :=
  w.dev.map (·.decryptQueue)

theorem decryptRing_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => decryptRing (project w)) a :=
  ha.of_factor (fun store : WGStoreView => store.dev.map (·.decryptQueue))
    (fun w => decryptRing (project w)) (fun _ => rfl)

theorem setPeer_decryptRing (pid : PeerId) (p : Peer) :
    SameView decryptRing (setPeer pid p) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [decryptRing, Option.map_map, Function.comp_def]

theorem getPeer_decryptRing (pid : PeerId) : SameView decryptRing (getPeer pid) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hr
  exact congrArg decryptRing (Peers.getPeer_current pid w v p ambient ambient' hr).1

theorem enqueue_rx_free_wp (before : Option (PtrRing SkbId)) (id : SkbId) :
    ⦃fun w => ⌜decryptRing w = before⌝⦄ enqueuePerDeviceAndPeerRx id
    ⦃⇓? ret _ => ⌜ret = 0 → FreeEntry before⌝⦄ := by
  let P := fun w : WGWorld => decryptRing w = before
  have packet_spec (id : SkbId) :
      Preserves P (setRxSkb id (fun p => {p with state := .uncrypted})) := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [P, decryptRing, hd] using hg
  have branch_spec (d : Decision) (b : Bool) (Q : WGWorld → Prop) :
      Hoare (branch d b : WG.M Bool) Q (fun x w => x = b ∧ Q w) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hq hr
    change Except.ok ((b, w), _) = Except.ok ((x, v), ambient') at hr
    cases hr
    exact ⟨rfl, hq⟩
  have device : Hoare getDev P
      (fun d w => P w ∧ before = some d.decryptQueue) := by
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
      exact ⟨hp, hp.symm.trans (by simp [decryptRing, hd])⟩
  have edit (f : Device → Device) (hf : ∀ d, (f d).decryptQueue = d.decryptQueue) :
      SameView decryptRing (modifyDev f) := by
    apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
    simp [decryptRing, Option.map_map, Function.comp_def, hf]
  have constant {α : Type} (a : WG.M α) (R : Prop) :
      Preserves (fun _ : WGWorld => R) a := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' h _
    exact h
  have returned (ret : Int) (Q : WGWorld → Prop)
      (hq : ∀ w, Q w → ret = 0 → FreeEntry before) :
      Hoare (pure ret : WG.M Int) Q (fun ret _ => ret = 0 → FreeEntry before) :=
    hoare_consequence (hoare_pure ret Q) (fun _ h => h)
      (fun _ w h => h.1 ▸ hq w h.2)
  have read_spec : Preserves P (getRxSkb id) := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [P, decryptRing, hd] using hg
  unfold enqueuePerDeviceAndPeerRx
  apply hoare_bind _ _ (packet_spec id)
  intro _
  apply hoare_bind _ _ read_spec
  intro pkt
  apply hoare_bind _ _ ((getPeer_decryptRing pkt.peer).wp (fun r => r = before))
  intro p
  apply hoare_bind _ _ (branch_spec .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS) P)
  intro refused
  cases refused with
  | true => exact returned _ _ (by intro _ _ he; cases he)
  | false =>
    apply hoare_consequence ?_ (fun _ h => h.2) (fun _ _ h => h)
    apply hoare_bind _ _ ((setPeer_decryptRing pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).wp
      (fun r => r = before))
    intro _
    apply hoare_bind _ _ device
    intro d
    let Q := fun r : Option (PtrRing SkbId) => r = before ∧ before = some d.decryptQueue
    apply hoare_bind _ _ ((decryptRing_kernel
      (Lifetimes.cpumaskNextOnlineFrom_sameStore d.decryptLastCpu)).wp Q)
    intro cpu
    apply hoare_bind _ _ ((edit (fun d => {d with decryptLastCpu := cpu}) (fun _ => rfl)).wp Q)
    intro _
    apply hoare_bind _ _ (branch_spec .enqueueRingFull d.decryptQueue.full
      (fun w => Q (decryptRing w)))
    intro full
    cases full with
    | true => exact returned _ _ (by intro _ _ he; cases he)
    | false =>
      exact hoare_consequence (constant _ (FreeEntry before))
        (fun _ h => ⟨d.decryptQueue, h.2.2, h.1.symm⟩)
        (fun _ _ h _ => h)

theorem enqueue_rx_success_free (id : SkbId) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeerRx id).run w).run ambient = .ok ((0, v), ambient')) :
    FreeEntry (decryptRing w) :=
  (hoare_iff_run_ambient _ _ _).mp (enqueue_rx_free_wp (decryptRing w) id) w ambient 0 v ambient' rfl hr rfl

end Leanux.Proofs.WG.Queues
