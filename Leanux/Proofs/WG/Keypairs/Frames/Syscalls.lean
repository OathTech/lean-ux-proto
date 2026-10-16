import Leanux.Proofs.Framing.Syscalls
import Leanux.Proofs.WG.Keypairs.OrdinaryRules
import Leanux.Proofs.WG.Keypairs.OrdinaryProduct

/-! Ordinary framing through syscall wrappers with an explicit contract for
the enclosed action; namespace descriptor closure preserves the snapshot. -/

namespace Leanux.Proofs.WG.Keypairs.SyscallFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open Leanux.Proofs.Framing

set_option maxHeartbeats 800000
set_option pp.structureInstances false

theorem socketCallOn_ordinary (fd : Nat) (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ProductOrdinaryAction (socketCallOn fd body) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have body_spec := hb.wp P hp
  have fsSpec {α : Type} (a : FS.M α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productFS_spec a _ (fun _ _ _ _ h => h)
  have ambientSpec {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have taskSpec {α : Type} (a : TaskM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productTask_spec a _ (fun _ _ _ h => h)
  unfold Hoare at fsSpec ambientSpec taskSpec
  mvcgen [-Std.Do.Spec.monadLift_StateT, socketCallOn,
    skipCut, unsupported, invariant, fsSpec, ambientSpec, taskSpec, body_spec]
  all_goals try exact (⇓? _ w => ⌜P (snapshot w.wg)⌝)
  all_goals simp_all


theorem socketCallOn_spec (P : Snapshot → Prop) (hp : Stable P)
    (fd : Nat) (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ socketCallOn fd body
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (socketCallOn_ordinary fd body hb).wp P hp

theorem socketCall_ordinary (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ProductOrdinaryAction (socketCall body) := socketCallOn_ordinary _ body hb

theorem socketCall_spec (P : Snapshot → Prop) (hp : Stable P)
    (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ socketCall body
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (socketCall_ordinary body hb).wp P hp

theorem netlinkRequest_ordinary (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ProductOrdinaryAction (netlinkRequest body) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have body_spec := hb.wp P hp
  have fsSpec {α : Type} (a : FS.M α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productFS_spec a _ (fun _ _ _ _ h => h)
  have ambientSpec {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have taskSpec {α : Type} (a : TaskM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productTask_spec a _ (fun _ _ _ h => h)
  unfold Hoare at fsSpec ambientSpec taskSpec
  mvcgen [-Std.Do.Spec.monadLift_StateT, netlinkRequest, socketCall, socketCallOn,
    skipCut, unsupported, invariant, fsSpec, ambientSpec, taskSpec, body_spec]
  all_goals try exact (⇓? _ w => ⌜P (snapshot w.wg)⌝)
  all_goals simp_all


theorem netlinkRequest_spec (P : Snapshot → Prop) (hp : Stable P)
    (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ netlinkRequest body
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (netlinkRequest_ordinary body hb).wp P hp

theorem rtnetlinkRequest_ordinary (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ProductOrdinaryAction (rtnetlinkRequest body) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have body_spec := hb.wp P hp
  have fsSpec {α : Type} (a : FS.M α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productFS_spec a _ (fun _ _ _ _ h => h)
  have ambientSpec {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have taskSpec {α : Type} (a : TaskM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productTask_spec a _ (fun _ _ _ h => h)
  unfold Hoare at fsSpec ambientSpec taskSpec
  mvcgen [-Std.Do.Spec.monadLift_StateT, rtnetlinkRequest, socketCallOn, getFiles, getTask, setFdtSlot, setFdtOpen, setFdtCloexec, modifyFdt, modifyFiles, modifyTask,
    skipCut, unsupported, invariant, fsSpec, ambientSpec, taskSpec, body_spec]
  all_goals try exact (⇓? _ w => ⌜P (snapshot w.wg)⌝)
  all_goals simp_all


theorem rtnetlinkRequest_spec (P : Snapshot → Prop) (hp : Stable P)
    (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ rtnetlinkRequest body
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (rtnetlinkRequest_ordinary body hb).wp P hp

theorem netnsClose_sameSnapshot :
    SameView (fun w : World => snapshot w.wg) netnsClose :=
  sameSnapshot_of_sameWGStore Framing.SyscallFrames.netnsClose_sameWGStore

theorem netnsClose_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ netnsClose
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := netnsClose_sameSnapshot.wp P

end Leanux.Proofs.WG.Keypairs.SyscallFrames
