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
  have fs {α : Type} (a : FS.M α) :
      ProductOrdinaryAction (MonadLift.monadLift a : Leanux.M α) :=
    SameView.ordinary (fun initial =>
      productFS_spec a (fun w => snapshot w.wg = initial) (fun _ _ _ _ h => h))
  unfold socketCallOn
  apply ordinary_bind (fs (fdget fd))
  intro f
  split
  · exact SameView.ordinary (SameView.pure _ _)
  · apply ordinary_bind hb
    intro ret
    exact ordinary_bind (fs (fdput f)) (fun _ => SameView.ordinary (SameView.pure _ ret))

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
  have ambient {α : Type} (a : AmbientM α) :
      ProductOrdinaryAction (MonadLift.monadLift a : Leanux.M α) :=
    SameView.ordinary (fun initial =>
      productAmbient_spec a (fun w => snapshot w.wg = initial) (fun _ _ h => h))
  unfold netlinkRequest
  apply ordinary_bind
  · apply socketCall_ordinary
    exact ordinary_bind (ambient (AmbientM.skipCut allocCuts)) (fun _ =>
      ordinary_bind hb (fun ret =>
        ordinary_bind (ambient (AmbientM.skipCut allocCuts)) (fun _ =>
          SameView.ordinary (SameView.pure _ ret))))
  · intro ret
    exact ordinary_bind (socketCall_ordinary _ (SameView.ordinary (SameView.pure _ 0)))
      (fun _ => SameView.ordinary (SameView.pure _ ret))

theorem netlinkRequest_spec (P : Snapshot → Prop) (hp : Stable P)
    (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ netlinkRequest body
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (netlinkRequest_ordinary body hb).wp P hp

theorem rtnetlinkRequest_ordinary (body : Leanux.M Int) (hb : ProductOrdinaryAction body) :
    ProductOrdinaryAction (rtnetlinkRequest body) := by
  have fs {α : Type} (a : FS.M α) :
      ProductOrdinaryAction (MonadLift.monadLift a : Leanux.M α) :=
    SameView.ordinary (fun initial =>
      productFS_spec a (fun w => snapshot w.wg = initial) (fun _ _ _ _ h => h))
  have ambient {α : Type} (a : AmbientM α) :
      ProductOrdinaryAction (MonadLift.monadLift a : Leanux.M α) :=
    SameView.ordinary (fun initial =>
      productAmbient_spec a (fun w => snapshot w.wg = initial) (fun _ _ h => h))
  have task {α : Type} (a : TaskM α) :
      ProductOrdinaryAction (MonadLift.monadLift a : Leanux.M α) :=
    SameView.ordinary (fun initial =>
      productTask_spec a (fun w => snapshot w.wg = initial) (fun _ _ _ h => h))
  unfold ProductOrdinaryAction
  have read : ProductOrdinaryAction (get : Leanux.M World) :=
    SameView.ordinary (fun initial => hoare_consequence
      (hoare_get (fun w => snapshot w.wg = initial)) (fun _ h => h) (fun _ _ h => h.2))
  unfold rtnetlinkRequest getFiles getTask modifyFiles modifyTask
  repeat' first
    | unfold ProductOrdinaryAction
    | (ordinary_head socketCallOn; apply socketCallOn_ordinary)
    | (ordinary_head Leanux.unsupported; exact ambient _)
    | (ordinary_head Leanux.skipCut; exact ambient _)
    | (ordinary_head MonadLift.monadLift; first | exact fs _ | exact task _ | exact ambient _)
    | (ordinary_head MonadLiftT.monadLift; first | exact fs _ | exact task _ | exact ambient _)
    | (ordinary_head liftM; unfold liftM)
    | (ordinary_head get; exact read)
    | (ordinary_head modify; apply ordinary_modify; intro w; exact Ordinary.refl _)
    | (ordinary_head Pure.pure; exact SameView.ordinary (SameView.pure _ _))
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | (ordinary_head Functor.discard; apply ordinary_discard)
    | keypairs_intro_forall
    | ordinary_head_reduce
    | ordinary_head_match
    | exact hb

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
