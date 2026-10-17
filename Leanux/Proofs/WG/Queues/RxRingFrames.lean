import Leanux.Proofs.WG.Queues.RxRingJournal
import Leanux.Proofs.WG.Queues.EnqueueAdmission
import Leanux.Proofs.Framing.Index
import Leanux.Proofs.Framing.WGIndex

/-! Exact deviceIndex/decrypt-ring frames for the original non-ring helpers.
Peer/keypair deletion is permitted; it does not delete the device ring. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

def nativeCell (w : WGWorld) : Option (Nat × PtrRing SkbId) :=
  w.dev.map fun d => (d.ifindex, d.decryptQueue)

theorem kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => nativeCell (project w)) a :=
  ha.of_factor (fun store : WGStoreView => store.dev.map (fun d => (d.ifindex, d.decryptQueue)))
    (fun w => nativeCell (project w)) (fun _ => rfl)

theorem modify (f : Device → Device) (he : ∀ d, (f d).ifindex = d.ifindex)
    (hq : ∀ d, (f d).decryptQueue = d.decryptQueue) : SameView nativeCell (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [nativeCell, Option.map_map, Function.comp_def, he, hq]

theorem getPeer_frame (pid : PeerId) : SameView nativeCell (getPeer pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [getPeer, getDev, invariant, AmbientM.invariant]

theorem getKeypair_frame (id : KeypairId) : SameView nativeCell (getKeypair id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getKeypair, getDev, invariant, AmbientM.invariant]

theorem setPeer_frame (pid : PeerId) (p : Peer) : SameView nativeCell (setPeer pid p) :=
  modify _ (fun _ => rfl) (fun _ => rfl)

theorem keypairGet_frame (id : Option KeypairId) : SameView nativeCell (keypairGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
    refcountIncNotZero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell]
  all_goals subst_vars
  all_goals simp_all

theorem keypairPut_frame (id : Option KeypairId) (now : Bool) : SameView nativeCell (keypairPut id now) := by
  apply SameView.of_wp
  intro s
  have hd := fun o => indexOwner_peerDeref_preserves o (fun w => nativeCell w = s)
  unfold Preserves Hoare at hd
  have hi {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at hi
  mvcgen [keypairPut, hd, hi, getKeypair, getDev, setKeypair, modifyDev,
    refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem peerGet_frame (id : PeerId) : SameView nativeCell (peerGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer, getDev, setPeer, modifyDev, refcountInc, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell]
  all_goals subst_vars
  all_goals simp_all

theorem peerGetMaybeZero_frame (id : Option PeerId) : SameView nativeCell (peerGetMaybeZero id) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGetMaybeZero, requireNotPending, getPeer, getDev, setPeer, modifyDev, refcountIncNotZero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell]
  all_goals subst_vars
  all_goals simp_all

theorem peerPut_frame (id : Option PeerId) : SameView nativeCell (peerPut id) := by
  apply SameView.of_wp
  intro s
  have hi {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at hi
  mvcgen [peerPut, hi, requireNotPending, getPeer, getDev, setPeer, modifyDev,
    refcountDecAndTest, retirePeerUnits, modifyAmbient, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem indexLookup_frame (kinds : List IndexKind) (index : Nat) : SameView nativeCell (indexLookup kinds index) := by
  apply SameView.of_wp
  intro s
  have hp := fun id => (peerGetMaybeZero_frame id).wp (fun t => t = s)
  have hb : Hoare (MonadLift.monadLift (indexBucket index) : WG.M (List IndexEntry)) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at hb
  mvcgen [indexLookup, IndexOwner.peerWord, IndexOwner.setPeerWord, getPeer, getKeypair,
    getDev, setPeer, setKeypair, modifyDev, hp, hb, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell]

theorem decryptPacket_frame (pkt : RxPacket) : SameView nativeCell (decryptPacket pkt) := by
  apply SameView.of_wp
  intro s
  have hc := fun d birth age => ((branchExpired_sameWGWorld d birth age).factor nativeCell).wp (fun t => t = s)
  have hh : Hoare (hiddenAlloc .skbCowDataRx : WG.M Bool)
      (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient (AmbientM.hiddenAlloc .skbCowDataRx) _
  unfold Hoare at hh
  mvcgen [decryptPacket, hc, hh, getKeypair, getDev, setKeypair, modifyDev,
    WG.orM, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell]
  all_goals subst_vars
  all_goals simp_all

end Leanux.Proofs.WG.Queues.RxRing
