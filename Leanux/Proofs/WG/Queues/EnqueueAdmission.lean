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
  have packet_spec := fun id => (setTxSkb_encryptRing id
    (fun p => {p with state := .uncrypted})).wp (fun r => r = before)
  have peer_spec := (getPeer_encryptRing pid).wp (fun r => r = before)
  have set_spec := fun p => (setPeer_encryptRing pid p).wp (fun r => r = before)
  have cpu_spec := fun cpu => (encryptRing_kernel
    (Lifetimes.cpumaskNextOnlineFrom_sameKernel cpu)).wp (fun r => r = before)
  have queue_spec := (encryptRing_kernel
    (Lifetimes.queueDeviceWork_sameKernel .encryptWorker)).wp (fun r => r = before)
  mvcgen [enqueuePerDeviceAndPeer, packet_spec, peer_spec, set_spec, cpu_spec,
    queue_spec, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [FreeEntry, encryptRing, EPIPE, ENOSPC, WG.EPIPE, WG.ENOSPC,
    Option.map_map, Function.comp_def]
  all_goals
    rename_i hfull hqueue
    refine ⟨_, ?_, hfull⟩
    symm
    assumption

theorem enqueue_success_free (pid : PeerId) (item : List SkbId) (w v : World)
    (hr : (enqueuePerDeviceAndPeer pid item).run w = .ok (0, v)) :
    FreeEntry (encryptRing w) :=
  (hoare_iff_triple _ _ _).mpr (enqueue_free_wp (encryptRing w) pid item) w 0 v rfl hr rfl

def decryptRing (w : World) : Option (PtrRing SkbId) :=
  w.k.wg.map (·.decryptQueue)

theorem decryptRing_kernel (ha : SameKernel a) : SameView decryptRing a := by
  intro w x v hr
  unfold decryptRing
  rw [ha w x v hr]

theorem setPeer_decryptRing (pid : PeerId) (p : Peer) :
    SameView decryptRing (setPeer pid p) := by
  intro w x v hr
  cases hr
  simp [decryptRing, Option.map_map, Function.comp_def]

theorem getPeer_decryptRing (pid : PeerId) : SameView decryptRing (getPeer pid) := by
  apply SameView.of_wp
  intro r
  mvcgen [getPeer, getDev, getK, invariant]

theorem getRxSkb_decryptRing (id : SkbId) : SameView decryptRing (getRxSkb id) := by
  apply SameView.of_wp
  intro r
  mvcgen [getRxSkb, getDev, getK, invariant]

theorem setRxSkb_decryptRing (id : SkbId) (f : RxPacket → RxPacket) :
    SameView decryptRing (setRxSkb id f) := by
  apply SameView.of_wp
  intro r
  mvcgen [setRxSkb, getRxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [decryptRing]

theorem enqueue_rx_free_wp (before : Option (PtrRing SkbId)) (id : SkbId) :
    ⦃fun w => ⌜decryptRing w = before⌝⦄ enqueuePerDeviceAndPeerRx id
    ⦃⇓? ret _ => ⌜ret = 0 → FreeEntry before⌝⦄ := by
  have packet_spec := (setRxSkb_decryptRing id
    (fun p => {p with state := .uncrypted})).wp (fun r => r = before)
  have read_spec := (getRxSkb_decryptRing id).wp (fun r => r = before)
  have peer_spec := fun pid => (getPeer_decryptRing pid).wp (fun r => r = before)
  have set_spec := fun pid p => (setPeer_decryptRing pid p).wp (fun r => r = before)
  have cpu_spec := fun cpu => (decryptRing_kernel
    (Lifetimes.cpumaskNextOnlineFrom_sameKernel cpu)).wp (fun r => r = before)
  have queue_spec := (decryptRing_kernel
    (Lifetimes.queueDeviceWork_sameKernel .decryptWorker)).wp (fun r => r = before)
  mvcgen [enqueuePerDeviceAndPeerRx, packet_spec, read_spec, peer_spec, set_spec, cpu_spec,
    queue_spec, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [FreeEntry, decryptRing, EPIPE, ENOSPC, WG.EPIPE, WG.ENOSPC,
    Option.map_map, Function.comp_def]
  all_goals
    rename_i hfull hqueue
    refine ⟨_, ?_, hfull⟩
    symm
    assumption

theorem enqueue_rx_success_free (id : SkbId) (w v : World)
    (hr : (enqueuePerDeviceAndPeerRx id).run w = .ok (0, v)) :
    FreeEntry (decryptRing w) :=
  (hoare_iff_triple _ _ _).mpr (enqueue_rx_free_wp (decryptRing w) id) w 0 v rfl hr rfl

end Leanux.Proofs.WG.Queues
