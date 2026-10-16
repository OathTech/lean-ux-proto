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
  apply SameView.of_wp
  intro r
  mvcgen [getPeer, getDev, invariant, AmbientM.invariant]

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
  have produce_map (ds : Option Device) (hr : ds.map (·.encryptQueue) = before) :
      ds.map (fun d => d.encryptQueue.produce item) = before.map (fun r => r.produce item) := by
    rw [← hr]
    cases ds <;> rfl
  mvcgen [enqueuePerDeviceAndPeer, packet_spec, peer_spec, set_spec, cpu_spec,
    queue_spec, getDev, modifyDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [EnqueueResult, encryptRing, EPIPE, ENOSPC, WG.EPIPE, WG.ENOSPC,
    Option.map_map, Function.comp_def]
  all_goals first
    | (apply produce_map; assumption)
    | (rename_i hfull; refine ⟨_, ?_, hfull⟩; symm; assumption)

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
