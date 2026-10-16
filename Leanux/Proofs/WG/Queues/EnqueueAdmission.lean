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
  have packet_spec (id : SkbId) :
      ⦃fun w => ⌜encryptRing w = before⌝⦄
        setTxSkb id (fun p => {p with state := .uncrypted})
      ⦃⇓? _ w => ⌜encryptRing w = before⌝⦄ := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [encryptRing, hd] using hg
  have peer_spec := (getPeer_encryptRing pid).wp (fun r => r = before)
  have set_spec := fun p => (setPeer_encryptRing pid p).wp (fun r => r = before)
  have cpu_spec := fun cpu => (encryptRing_kernel
    (Lifetimes.cpumaskNextOnlineFrom_sameStore cpu)).wp (fun r => r = before)
  have queue_spec :
      ⦃fun w => ⌜encryptRing w = before⌝⦄ (queueDeviceWork .encryptWorker : WG.M Unit)
      ⦃⇓? _ w => ⌜encryptRing w = before⌝⦄ :=
    hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker) (fun w => encryptRing w = before)
  mvcgen [enqueuePerDeviceAndPeer, packet_spec, peer_spec, set_spec, cpu_spec,
    queue_spec, getDev, modifyDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [FreeEntry, encryptRing, EPIPE, ENOSPC, WG.EPIPE, WG.ENOSPC,
    Option.map_map, Function.comp_def]
  all_goals
    rename_i hfull hqueue
    refine ⟨_, ?_, hfull⟩
    symm
    assumption

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
  apply SameView.of_wp
  intro r
  mvcgen [getPeer, getDev, invariant, AmbientM.invariant]

theorem enqueue_rx_free_wp (before : Option (PtrRing SkbId)) (id : SkbId) :
    ⦃fun w => ⌜decryptRing w = before⌝⦄ enqueuePerDeviceAndPeerRx id
    ⦃⇓? ret _ => ⌜ret = 0 → FreeEntry before⌝⦄ := by
  have packet_spec :
      ⦃fun w => ⌜decryptRing w = before⌝⦄
        setRxSkb id (fun p => {p with state := .uncrypted})
      ⦃⇓? _ w => ⌜decryptRing w = before⌝⦄ := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [decryptRing, hd] using hg
  have read_spec :
      ⦃fun w => ⌜decryptRing w = before⌝⦄ getRxSkb id
      ⦃⇓? _ w => ⌜decryptRing w = before⌝⦄ := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [decryptRing, hd] using hg
  have peer_spec := fun pid => (getPeer_decryptRing pid).wp (fun r => r = before)
  have set_spec := fun pid p => (setPeer_decryptRing pid p).wp (fun r => r = before)
  have cpu_spec := fun cpu => (decryptRing_kernel
    (Lifetimes.cpumaskNextOnlineFrom_sameStore cpu)).wp (fun r => r = before)
  have queue_spec :
      ⦃fun w => ⌜decryptRing w = before⌝⦄ (queueDeviceWork .decryptWorker : WG.M Unit)
      ⦃⇓? _ w => ⌜decryptRing w = before⌝⦄ :=
    hoare_liftAmbient (AmbientM.queueDeviceWork .decryptWorker) (fun w => decryptRing w = before)
  mvcgen [enqueuePerDeviceAndPeerRx, packet_spec, read_spec, peer_spec, set_spec, cpu_spec,
    queue_spec, getDev, modifyDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [FreeEntry, decryptRing, EPIPE, ENOSPC, WG.EPIPE, WG.ENOSPC,
    Option.map_map, Function.comp_def]
  all_goals
    rename_i hfull hqueue
    refine ⟨_, ?_, hfull⟩
    symm
    assumption

theorem enqueue_rx_success_free (id : SkbId) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeerRx id).run w).run ambient = .ok ((0, v), ambient')) :
    FreeEntry (decryptRing w) :=
  (hoare_iff_run_ambient _ _ _).mp (enqueue_rx_free_wp (decryptRing w) id) w ambient 0 v ambient' rfl hr rfl

end Leanux.Proofs.WG.Queues
