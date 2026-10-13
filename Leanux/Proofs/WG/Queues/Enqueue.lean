import Leanux.Proofs.WG.Lifetimes.ReceiveEntry
import Leanux.Proofs.WG.Queues.PtrRing

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Original TX enqueue result refinement. Peer-queue refusal precedes the
ring-full test; queue-work failures remain errors, not ordinary return codes.
No well-formedness, ownership, or reachability premise is used. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def encryptRing (w : World) : Option (PtrRing (List SkbId)) :=
  w.k.wg.map (·.encryptQueue)

theorem encryptRing_kernel (ha : SameKernel a) : SameView encryptRing a := by
  intro w x v hr
  unfold encryptRing
  rw [ha w x v hr]

theorem setPeer_encryptRing (pid : PeerId) (p : Peer) :
    SameView encryptRing (setPeer pid p) := by
  intro w x v hr
  cases hr
  simp [encryptRing, Option.map_map, Function.comp_def]

theorem setTxSkb_encryptRing (id : SkbId) (f : DataPacket → DataPacket) :
    SameView encryptRing (setTxSkb id f) := by
  apply SameView.of_wp
  intro r
  mvcgen [setTxSkb, getTxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [encryptRing]

theorem getPeer_encryptRing (pid : PeerId) : SameView encryptRing (getPeer pid) := by
  apply SameView.of_wp
  intro r
  mvcgen [getPeer, getDev, getK, invariant]

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
  have packet_spec := fun id => (setTxSkb_encryptRing id
    (fun p => {p with state := .uncrypted})).wp (fun r => r = before)
  have peer_spec := (getPeer_encryptRing pid).wp (fun r => r = before)
  have set_spec := fun p => (setPeer_encryptRing pid p).wp (fun r => r = before)
  have cpu_spec := fun cpu => (encryptRing_kernel
    (Lifetimes.cpumaskNextOnlineFrom_sameKernel cpu)).wp (fun r => r = before)
  have queue_spec := (encryptRing_kernel
    (Lifetimes.queueDeviceWork_sameKernel .encryptWorker)).wp
      (fun r => r = before)
  have produce_map (ds : Option Device) (hr : ds.map (·.encryptQueue) = before) :
      ds.map (fun d => d.encryptQueue.produce item) = before.map (fun r => r.produce item) := by
    rw [← hr]
    cases ds <;> rfl
  mvcgen [enqueuePerDeviceAndPeer, packet_spec, peer_spec, set_spec, cpu_spec,
    queue_spec, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [EnqueueResult, encryptRing, EPIPE, ENOSPC, WG.EPIPE, WG.ENOSPC,
    Option.map_map, Function.comp_def]
  all_goals first
    | (apply produce_map; assumption)
    | (rename_i hfull; refine ⟨_, ?_, hfull⟩; symm; assumption)

theorem enqueue_ring_result (pid : PeerId) (item : List SkbId)
    (w v : World) (ret : Int)
    (hr : (enqueuePerDeviceAndPeer pid item).run w = .ok (ret, v)) :
    EnqueueResult (encryptRing w) item ret (encryptRing v) :=
  (hoare_iff_triple _ _ _).mpr (enqueue_ring_wp (encryptRing w) pid item)
    w ret v rfl hr

theorem enqueue_epipe (pid : PeerId) (item : List SkbId) (w v : World)
    (hr : (enqueuePerDeviceAndPeer pid item).run w = .ok (-EPIPE, v)) :
    encryptRing v = encryptRing w ∧
      ∃ r, encryptRing w = some r ∧ r.full = true := by
  have h := enqueue_ring_result pid item w v (-EPIPE) hr
  simpa [EnqueueResult, EPIPE, ENOSPC] using h

end Leanux.Proofs.WG.Queues
