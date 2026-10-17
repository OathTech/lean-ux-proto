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
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

abbrev Event := Ring.Journal.Event (List SkbId)
abbrev Obs := PrefixM Event

def nativeCell (w : WGWorld) : Option (Nat × PtrRing (List SkbId)) :=
  w.dev.map fun d => (d.ifindex, d.encryptQueue)

def cell (w : World) : Option (Nat × PtrRing (List SkbId)) := nativeCell w.wg

abbrev Refines := Ring.Source.Refines (ι := List SkbId)
abbrev Safe := Ring.Source.Safe (ι := List SkbId)
abbrev Inv := Ring.Source.Inv cell
abbrev Initialized := Ring.Source.Initialized (ι := List SkbId)

theorem kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => nativeCell (project w)) a :=
  ha.of_factor (fun store : WGStoreView => store.dev.map (fun d => (d.ifindex, d.encryptQueue)))
    (fun w => nativeCell (project w)) (fun _ => rfl)

theorem modify (f : Device → Device) (he : ∀ d, (f d).ifindex = d.ifindex)
    (hq : ∀ d, (f d).encryptQueue = d.encryptQueue) : SameView nativeCell (modifyDev f) := by
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

theorem cpu_frame (pid : PeerId) : SameView nativeCell (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_frame pid p).wp (fun t => t = s)
  mvcgen [cpumaskChooseOnline, hg, hs, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell]

theorem enqueuePeer_frame (item : List SkbId) (state : PacketState) :
    SameView nativeCell (enqueuePerPeerTx item state) := by
  apply SameView.of_wp
  intro s
  have hk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have hp := fun id => (getPeer_frame id).wp (fun t => t = s)
  have hg := fun id => (peerGet_frame id).wp (fun t => t = s)
  have hu := fun id => (peerPut_frame id).wp (fun t => t = s)
  have hc := fun id => (cpu_frame id).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  have packet {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [nativeCell, hd] using hg
  unfold Hoare at ambient packet
  have hm := fun id => (modify (fun d => {d with txWorkQueue := d.txWorkQueue ++ [id]})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  have hw := fun o => indexOwner_peerDeref_preserves o (fun w => nativeCell w = s)
  unfold Preserves Hoare at hw
  mvcgen [-Std.Do.Spec.monadLift_StateT, hw, enqueuePerPeerTx, packet, ambient, hk, hp, hg, hu, hc, hm,
    getDev, getTxSkb, setTxSkb, recordQueued, peekQueuedUnit, branch, AmbientM.branch,
    invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals simp_all [nativeCell]

end Leanux.Proofs.WG.Queues.TxRing
