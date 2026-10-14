import Leanux.Proofs.WG.Queues.RingSource
import Leanux.Proofs.Framing.WGData
import Leanux.Proofs.WG.Queues.EnqueueAdmission
import Leanux.Proofs.Framing.Index
import Leanux.Proofs.Framing.WGIndex

/-! Exact deviceIndex/encrypt-ring frames for the original non-ring helpers.
Peer/keypair deletion is permitted; it does not delete the device ring. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

abbrev Event := Ring.Journal.Event (List SkbId)
abbrev Obs := PrefixM Event

def cell (w : World) : Option (Nat × PtrRing (List SkbId)) :=
  w.k.wg.map fun d => (d.ifindex, d.encryptQueue)

abbrev Refines := Ring.Source.Refines (ι := List SkbId)
abbrev Safe := Ring.Source.Safe (ι := List SkbId)
abbrev Inv := Ring.Source.Inv cell
abbrev Initialized := Ring.Source.Initialized (ι := List SkbId)

theorem kernel (ha : SameKernel a) : SameView cell a := by
  intro w x v hr
  unfold cell
  rw [ha w x v hr]

theorem modify (f : Device → Device) (he : ∀ d, (f d).ifindex = d.ifindex)
    (hq : ∀ d, (f d).encryptQueue = d.encryptQueue) : SameView cell (modifyDev f) := by
  intro w x v hr
  cases hr
  simp [cell, Option.map_map, Function.comp_def, he, hq]

theorem getPeer_frame (pid : PeerId) : SameView cell (getPeer pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [getPeer, getDev, getK, invariant]

theorem getKeypair_frame (id : KeypairId) : SameView cell (getKeypair id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getKeypair, getDev, getK, invariant]

theorem getTx_frame (id : SkbId) : SameView cell (getTxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getTxSkb, getDev, getK, invariant]

theorem setPeer_frame (pid : PeerId) (p : Peer) : SameView cell (setPeer pid p) :=
  modify _ (fun _ => rfl) (fun _ => rfl)

theorem setTx_frame (id : SkbId) (f : DataPacket → DataPacket) : SameView cell (setTxSkb id f) := by
  unfold setTxSkb
  exact (getTx_frame id).bind fun _ => modify _ (fun _ => rfl) (fun _ => rfl)

theorem freeTx_frame (id : SkbId) : SameView cell (freeTxSkb id) := by
  unfold freeTxSkb
  exact (getTx_frame id).bind fun _ => modify _ (fun _ => rfl) (fun _ => rfl)

theorem keypairPut_frame (id : Option KeypairId) (now : Bool) : SameView cell (keypairPut id now) := by
  apply SameView.of_wp
  intro s
  simp only [keypairPut, indexRemoveKeypair_eq]
  mvcgen [indexUnhash, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    refcountDecAndTest, branch, branchCmp, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem peerGet_frame (id : PeerId) : SameView cell (peerGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer, getDev, getK, setPeer, modifyDev,
    modifyK, refcountInc, branch, branchCmp, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem peerPut_frame (id : Option PeerId) : SameView cell (peerPut id) := by
  apply SameView.of_wp
  intro s
  simp only [peerPut, indexRemove_eq]
  mvcgen [indexUnhash, requireNotPending, getPeer, getDev, getK, setPeer, modifyDev,
    modifyK, refcountDecAndTest, retirePeerUnits, branch, branchCmp, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem invariant_frame (why : String) : SameView cell (invariant (α := α) why) := by
  intro w x v hr
  cases hr

theorem cpu_frame (pid : PeerId) : SameView cell (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_frame pid p).wp (fun t => t = s)
  mvcgen [cpumaskChooseOnline, hg, hs, branch]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell]

theorem enqueuePeer_frame (item : List SkbId) (state : PacketState) :
    SameView cell (enqueuePerPeerTx item state) := by
  apply SameView.of_wp
  intro s
  have ht := fun id => (getTx_frame id).wp (fun t => t = s)
  have hk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have hp := fun id => (getPeer_frame id).wp (fun t => t = s)
  have hg := fun id => (peerGet_frame id).wp (fun t => t = s)
  have hu := fun id => (peerPut_frame id).wp (fun t => t = s)
  have hs := fun id f => (setTx_frame id f).wp (fun t => t = s)
  have hc := fun id => (cpu_frame id).wp (fun t => t = s)
  have hpeek := fun id => (kernel (peekQueuedUnit_sameKernel .txWorker id)).wp (fun t => t = s)
  have hrec := fun id => (kernel (Lifetimes.recordQueued_sameKernel .txWorker id)).wp (fun t => t = s)
  have hm := fun id => (modify (fun d => {d with txWorkQueue := d.txWorkQueue ++ [id]})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [enqueuePerPeerTx, ht, hk, hp, hg, hu, hs, hc, hpeek, hrec, hm,
    getDev, getK, invariant]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals simp_all [cell]

end Leanux.Proofs.WG.Queues.TxRing
