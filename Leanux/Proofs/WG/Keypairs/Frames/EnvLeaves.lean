import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Keypairs.Frames.WGDevice
import Leanux.Env
import Leanux.Proofs.Framing.Stack
import Leanux.Proofs.Framing.WGData
import Leanux.Proofs.Framing.Batch
import Leanux.Proofs.Framing.EnvLeaves
import Leanux.Proofs.WG.Keypairs.SnapshotRules
import Leanux.Proofs.WG.Keypairs.OrdinaryProduct

/-! Framing the inner IP delivery cut and scheduler/environment leaves. -/
namespace Leanux.Proofs.WG.Keypairs.EnvFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open WGFrames WGTransitions WGMore WGConfig WGDevice

set_option maxHeartbeats 400000

private theorem productStore_snapshot {a : Leanux.M α} (h : Framing.SameProductStore a) :
    Framing.SameView (fun w : World => snapshot w.wg) a :=
  h.of_factor
    (fun s : Framing.ProductStore43 =>
      (⟨s.2.2.2.keypairCounter, fun i => (s.2.2.2.dev.bind fun d => d.keypairs[i]?).map cell⟩ : Snapshot))
    (fun w => snapshot w.wg) (fun _ => rfl)


theorem excluded_sameSnapshot (row : String) :
    Framing.SameView (fun w : World => snapshot w.wg) (Leanux.Env.Stack.excluded row) := by
  apply (Lifetimes.ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  obtain ⟨e, he⟩ := Framing.stackExcluded_failure row w
  rw [he] at hr
  contradiction

theorem excluded_spec (P : Snapshot → Prop) (row : String) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Leanux.Env.Stack.excluded row)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (excluded_sameSnapshot row).wp P

theorem reply4_ordinary (dst : Nat) (bytes : List UInt8) :
    ProductOrdinaryAction (Leanux.Env.Stack.reply4 dst bytes) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have ha := fun α (a : AmbientM α) => Framing.productAmbient_spec a
    (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  have hd := (Framing.sameView_liftWG (fun w => snapshot w.wg) snapshot getDev
    getDev_sameSnapshot (fun _ _ _ h => h)).wp P
  have hr (src dst : Nat) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (MonadLift.monadLift (Net.routeOutput4 src dst) : WG.M _) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    (productStore_snapshot (Framing.liftWG_sameProductStore _ (Framing.liftRouting_sameWGStore _))).wp P
  have hn (index : Nat) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (MonadLift.monadLift (Net.neighbourClassify index) : WG.M _) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    (productStore_snapshot (Framing.liftWG_sameProductStore _ (Framing.liftRouting_sameWGStore _))).wp P
  have hx (f a : Nat) (ps : List Packet) (mtu : Nat) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (MonadLift.monadLift (wgXmit f a ps mtu) : Leanux.M _)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    Lifetimes.ProjectedAction.wp (OrdinaryAction.liftWG (wgXmit_ordinary f a ps mtu)) P hp
  have discardSpec := Framing.discard_view_spec (α := Int) (m := Except Stop) (fun w : World => snapshot w.wg) P
  unfold Framing.Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.Stack.reply4,
    skipCut, hd, hr, hn, hx, ha, unsupported, discardSpec]

theorem reply4_spec (P : Snapshot → Prop) (hp : Stable P) (dst : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Leanux.Env.Stack.reply4 dst bytes)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (reply4_ordinary dst bytes).wp P hp

private def envHeadBZ : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n+1, e =>
    let e := e.consumeMData
    match e with
    | .letE _ _ v b _ => envHeadBZ n (b.instantiate1 v)
    | _ =>
      match e.getAppFn.consumeMData with
      | .letE _ _ v b _ => envHeadBZ n (Lean.mkAppN (b.instantiate1 v) e.getAppArgs)
      | .lam .. =>
        let e' := e.headBeta
        if Lean.Expr.equal e e' then e else envHeadBZ n e'
      | _ => e

elab "env_ordinary_head_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
  let .app f a := t | Lean.throwError "missing action"
  let a' := envHeadBZ 64 a
  if Lean.Expr.equal a a' then Lean.throwError "unchanged head"
  Lean.Elab.Tactic.replaceMainGoal [← g.replaceTargetDefEq (.app f a')]

elab "env_ordinary_head_match" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
  unless t.getAppArgs.size > 0 do Lean.throwError "no action argument"
  let a := t.getAppArgs.back! |>.consumeMData
  let some _ ← Lean.Meta.matchMatcherApp? a | Lean.throwError "not a head matcher"
  Lean.Elab.Tactic.replaceMainGoal (← Lean.Meta.Split.splitMatch g a)

elab "env_bind_head " n:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.getAppArgs.size > 0 do Lean.throwError "no action argument"
  let a := t.getAppArgs.back! |>.consumeMData
  unless a.isAppOf (Lean.Name.mkStr2 "Bind" "bind") do Lean.throwError "not a bind"
  let args := a.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing bind arguments"
  let first := args[args.size - 2]!.consumeMData
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless first.isAppOf name do Lean.throwError "different first action"

theorem receive4_ordinary (pkt : List UInt8) : ProductOrdinaryAction (Leanux.Env.Stack.receive4 pkt) := by
  have stopped (a : Leanux.M Unit) (failure : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : ProductOrdinaryAction (a >>= tail) := by
    apply (Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := failure w
    simp only [StateT.run_bind, he, Except.bind] at hr
    contradiction
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (Framing.stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_, rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_, rfl⟩) tail
  have route (src dst : Nat) : ProductOrdinaryAction
      (MonadLift.monadLift (MonadLift.monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    SameView.ordinary (productStore_snapshot
      (Framing.liftWG_sameProductStore _ (Framing.liftRouting_sameWGStore _)))
  have read : ProductOrdinaryAction (getWG : Leanux.M WGWorld) := by
    apply (Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    exact .refl _
  have write (f : EnvWorld → EnvWorld) : ProductOrdinaryAction (modifyEnv f) := by
    apply (Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    exact .refl _
  unfold ProductOrdinaryAction
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (ordinary_head Leanux.Env.Stack.excluded; exact SameView.ordinary (excluded_sameSnapshot _))
    | (ordinary_head Leanux.Env.Stack.reply4; exact reply4_ordinary _ _)
    | (ordinary_head MonadLift.monadLift; exact route _ _)
    | (ordinary_head liftM; exact route _ _)
    | (ordinary_head getWG; exact read)
    | (ordinary_head modifyEnv; exact write _)
    | (ordinary_head Pure.pure; exact SameView.ordinary (Framing.SameView.pure _ _))
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | keypairs_intro_forall
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem receive4_spec (P : Snapshot → Prop) (hp : Stable P) (pkt : List UInt8) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Leanux.Env.Stack.receive4 pkt)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (receive4_ordinary pkt).wp P hp

theorem receive6_sameSnapshot (pkt : List UInt8) : Framing.SameView (fun w : World => snapshot w.wg) (Leanux.Env.Stack.receive6 pkt) :=
  productStore_snapshot (Framing.stackReceive6_sameKernel pkt)

theorem receive6_spec (P : Snapshot → Prop) (pkt : List UInt8) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Leanux.Env.Stack.receive6 pkt)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (receive6_sameSnapshot pkt).wp P

theorem receive_ordinary (pkt : List UInt8) : ProductOrdinaryAction (Leanux.Env.Stack.receive pkt) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have six := receive6_spec P
  have four := receive4_spec P hp
  have ha := fun α (a : AmbientM α) => Framing.productAmbient_spec a
    (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  unfold Framing.Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.Stack.receive, six, four, ha, invariant]
  all_goals try trivial

theorem receive_spec (P : Snapshot → Prop) (hp : Stable P) (pkt : List UInt8) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Leanux.Env.Stack.receive pkt)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (receive_ordinary pkt).wp P hp

theorem deliverInner_ordinary (pkt : List UInt8) : ProductOrdinaryAction (Leanux.Env.deliverInner pkt) := by
  exact receive_ordinary pkt

theorem deliverInner_spec (P : Snapshot → Prop) (hp : Stable P) (pkt : List UInt8) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Leanux.Env.deliverInner pkt)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (deliverInner_ordinary pkt).wp P hp

theorem checksumHelp_sameSnapshot (pkt : Packet) : Framing.SameView (fun w : World => snapshot w.wg) (Leanux.Env.checksumHelp pkt) :=
  (Framing.checksumHelp_sameWorld pkt).of_factor (fun w => snapshot w.wg) (fun w => snapshot w.wg) (fun _ => rfl)

theorem checksumHelp_spec (P : Snapshot → Prop) (pkt : Packet) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Leanux.Env.checksumHelp pkt)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (checksumHelp_sameSnapshot pkt).wp P

theorem deliverSent_sameSnapshot  : Framing.SameView (fun w : World => snapshot w.wg) Leanux.Env.deliverSent :=
  productStore_snapshot Framing.deliverSent_sameKernel

theorem deliverSent_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Leanux.Env.deliverSent
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (deliverSent_sameSnapshot ).wp P

theorem peekNextSite_sameSnapshot  : Framing.SameView (fun w : World => snapshot w.wg) Leanux.Env.peekNextSite :=
  productStore_snapshot Framing.peekNextSite_sameKernel

theorem peekNextSite_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Leanux.Env.peekNextSite
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (peekNextSite_sameSnapshot ).wp P

theorem senderSource_sameSnapshot (family dest tos : Nat) (ll : Bool) :
    Framing.SameView (fun w : World => snapshot w.wg) (Leanux.Env.senderSource family dest tos ll) :=
  productStore_snapshot (Framing.senderSource_sameKernel family dest tos ll)

theorem senderSource_spec (P : Snapshot → Prop) (family dest tos : Nat) (ll : Bool) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Leanux.Env.senderSource family dest tos ll
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (senderSource_sameSnapshot family dest tos ll).wp P

theorem fixtureSend_sameSnapshot : Framing.SameView (fun w : World => snapshot w.wg) Leanux.Env.fixtureSend :=
  by
    intro initial
    exact Framing.productAmbient_spec (AmbientM.skipCut _) (fun w => snapshot w.wg = initial) (fun _ _ h => h)

theorem fixtureSend_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Leanux.Env.fixtureSend
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := fixtureSend_sameSnapshot.wp P

theorem condResched_sameSnapshot (self : Worker) : Framing.SameView (fun w : World => snapshot w.wg) (Env.condResched self) :=
  productStore_snapshot (Framing.condResched_sameKernel self)

theorem condResched_spec (P : Snapshot → Prop) (self : Worker) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.condResched self
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (condResched_sameSnapshot self).wp P

theorem activationHasWork_sameSnapshot (a : Activation) : Framing.SameView (fun w : World => snapshot w.wg) (Env.Activation.hasWork a) :=
  productStore_snapshot (Framing.activationHasWork_sameKernel a)

theorem activationHasWork_spec (P : Snapshot → Prop) (a : Activation) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.Activation.hasWork a
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (activationHasWork_sameSnapshot a).wp P

theorem activationOccupancy_sameSnapshot (a : Activation) : Framing.SameView (fun w : World => snapshot w.wg) (Env.Activation.occupancy a) :=
  productStore_snapshot (Framing.activationOccupancy_sameKernel a)

/-- The trial executes on a copy; its returned World is discarded. -/
theorem activationConsistent_sameSnapshot (a : Activation) : Framing.SameView (fun w : World => snapshot w.wg) (Env.Activation.consistent a) :=
  productStore_snapshot (Framing.activationConsistent_sameKernel a)

theorem activationConsistent_spec (P : Snapshot → Prop) (a : Activation) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.Activation.consistent a
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (activationConsistent_sameSnapshot a).wp P

theorem filterAuxM_sameSnapshot (f : α → Leanux.M Bool) (hf : ∀ a, Framing.SameView (fun w : World => snapshot w.wg) (f a))
    (xs acc : List α) : Framing.SameView (fun w : World => snapshot w.wg) (List.filterAuxM f xs acc) := by
  induction xs generalizing acc with
  | nil => exact Framing.SameView.pure _ _
  | cons a xs ih =>
    exact snapshot_bind (hf a) (fun b => ih (cond b (a :: acc) acc))

theorem filterM_sameSnapshot (f : α → Leanux.M Bool) (hf : ∀ a, Framing.SameView (fun w : World => snapshot w.wg) (f a))
    (xs : List α) : Framing.SameView (fun w : World => snapshot w.wg) (xs.filterM f) := by
  exact snapshot_bind (filterAuxM_sameSnapshot f hf xs []) (fun ys => Framing.SameView.pure _ ys.reverse)

end Leanux.Proofs.WG.Keypairs.EnvFrames
