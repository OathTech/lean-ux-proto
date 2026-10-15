import Leanux.Proofs.WG.Queues.RxRingJournal
import Leanux.Proofs.WG.Queues.EnqueueAdmission
import Leanux.Proofs.Framing.Index
import Leanux.Proofs.Framing.WGIndex

/-! Exact deviceIndex/decrypt-ring frames for the original non-ring helpers.
Peer/keypair deletion is permitted; it does not delete the device ring. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem kernel (ha : SameKernel a) : SameView cell a := by
  intro w x v hr
  unfold cell
  rw [ha w x v hr]

theorem modify (f : Device → Device) (he : ∀ d, (f d).ifindex = d.ifindex)
    (hq : ∀ d, (f d).decryptQueue = d.decryptQueue) : SameView cell (modifyDev f) := by
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

theorem getRx_frame (id : SkbId) : SameView cell (getRxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getRxSkb, getDev, getK, invariant]

theorem setPeer_frame (pid : PeerId) (p : Peer) : SameView cell (setPeer pid p) :=
  modify _ (fun _ => rfl) (fun _ => rfl)

theorem setRx_frame (id : SkbId) (f : RxPacket → RxPacket) : SameView cell (setRxSkb id f) := by
  unfold setRxSkb
  exact (getRx_frame id).bind fun _ => modify _ (fun _ => rfl) (fun _ => rfl)

theorem newRx_frame (p : RxPacket) : SameView cell (newRxSkb p) := by
  apply SameView.of_wp
  intro s
  mvcgen [newRxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem freeRx_frame (id : SkbId) : SameView cell (freeRxSkb id) := by
  unfold freeRxSkb
  exact (getRx_frame id).bind fun _ => modify _ (fun _ => rfl) (fun _ => rfl)

theorem keypairGet_frame (id : Option KeypairId) : SameView cell (keypairGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [keypairGet, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    refcountIncNotZero, branch, branchCmp, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem keypairPut_frame (id : Option KeypairId) (now : Bool) : SameView cell (keypairPut id now) := by
  apply SameView.of_wp
  intro s
  simp only [keypairPut, indexRemove_eq]
  have hd := fun o k => sameKernel_wp _ (indexOwner_peerDeref_sameKernel o) (fun v => v = k)
  mvcgen [hd, indexUnhash, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
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

theorem peerGetMaybeZero_frame (id : Option PeerId) : SameView cell (peerGetMaybeZero id) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGetMaybeZero, requireNotPending, getPeer, getDev, getK, setPeer, modifyDev,
    modifyK, refcountIncNotZero, branch, branchCmp, invariant, unsupported]
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

theorem indexLookup_frame (kinds : List IndexKind) (index : Nat) : SameView cell (indexLookup kinds index) := by
  apply SameView.of_wp
  intro s
  have hp := fun id => (peerGetMaybeZero_frame id).wp (fun t => t = s)
  have hb := (kernel (indexBucket_sameKernel index)).wp (fun t => t = s)
  mvcgen [indexLookup, IndexOwner.peerWord, IndexOwner.setPeerWord, getPeer, getKeypair, getDev, getK, setPeer, setKeypair, modifyDev, modifyK, hp, hb, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell]

theorem decryptPacket_frame (pkt : RxPacket) : SameView cell (decryptPacket pkt) := by
  apply SameView.of_wp
  intro s
  have hc := fun d birth age => (kernel (branchExpired_sameKernel d birth age)).wp (fun t => t = s)
  have hh := (kernel (hiddenAlloc_sameKernel .skbCowDataRx)).wp (fun t => t = s)
  mvcgen [decryptPacket, hc, hh, getKeypair, getDev, getK, setKeypair, modifyDev,
    modifyK, WG.orM, branch, branchCmp, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

end Leanux.Proofs.WG.Queues.RxRing
