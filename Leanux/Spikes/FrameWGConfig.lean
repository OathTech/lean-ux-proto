import Leanux.Spikes.FrameWGMore

/-! Framing the two configuration callers while sharing the contracts of
compiler-generated continuations. All tactic output is checked by Lean. -/

namespace Leanux.Spikes.Lifetimes.WGConfig
open Leanux Leanux.WG Std.Do Leanux.Spikes.Lifetimes Leanux.Spikes.Lifetimes.KernelFrames Leanux.Spikes.Lifetimes.WGFrames Leanux.Spikes.Lifetimes.WGTransitions Leanux.Spikes.Lifetimes.WGMore

set_option maxHeartbeats 200000
set_option pp.structureInstances false

open Lean Meta Elab Tactic

private def ordinaryHeadBZ : Nat → Expr → Expr
  | 0, e => e
  | n+1, e =>
    let e := e.consumeMData
    match e with
    | .letE _ _ v b _ => ordinaryHeadBZ n (b.instantiate1 v)
    | _ =>
      match e.getAppFn.consumeMData with
      | .letE _ _ v b _ => ordinaryHeadBZ n (mkAppN (b.instantiate1 v) e.getAppArgs)
      | .lam .. =>
        let e' := e.headBeta
        if Expr.equal e e' then e else ordinaryHeadBZ n e'
      | _ => e

elab "ordinary_head_reduce" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``OrdinaryAction do throwError "not OrdinaryAction"
  let .app f a := t | throwError "missing action"
  let a' := ordinaryHeadBZ 64 a
  if Expr.equal a a' then throwError "head unchanged"
  replaceMainGoal [← g.replaceTargetDefEq (.app f a')]

elab "ordinary_head_match" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``OrdinaryAction do throwError "not OrdinaryAction"
  let a := t.getAppArgs.back! |>.consumeMData
  let some _ ← Lean.Meta.matchMatcherApp? a | throwError "not a top matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch g a)


/-- Prove each compiler-generated continuation once, then use its contract. -/
elab "ordinary_join_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``OrdinaryAction do throwError "not OrdinaryAction"
  let action := target.getAppArgs.back! |>.consumeMData
  let .letE name ty value body _ := action | throwError "not a let"
  unless name.toString.startsWith "__do_jp" do throwError "not a join continuation"
  let property ← forallTelescope ty fun args _ => do
    let result ← mkAppM ``OrdinaryAction #[mkAppN value args]
    mkForallFVars args result
  let valueProof ← mkFreshExprSyntheticOpaqueMVar property
  let (continuation, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun args _ => do
      let result ← mkAppM ``OrdinaryAction #[mkAppN f args]
      mkForallFVars args result
    withLocalDeclD `ordinary_join contract fun hf => do
      let bodyProp ← mkAppM ``OrdinaryAction #[body.instantiate1 f]
      let next ← mkFreshExprSyntheticOpaqueMVar bodyProp
      let proof ← mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (mkApp2 continuation value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "ordinary_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``OrdinaryAction do throwError "not OrdinaryAction"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `ordinary_join then
      let proof := mkAppN decl.toExpr action.getAppArgs
      try
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
      catch _ => pure ()
  throwError "no continuation contract"

macro "ordinary_strict_step" : tactic => `(tactic|
  first
    | contradiction
    | intro_forall
    | with_reducible assumption
    | ordinary_join_let
    | ordinary_join_use
    | (ordinary_head Pure.pure; exact ordinary_pure _)
    | (ordinary_head MonadExceptOf.throw; exact ordinary_throw _)
    | (ordinary_head get; exact ordinary_get)
    | (ordinary_head modify; refine ordinary_modify _ ?_; intro w; exact Ordinary.refl _)
    | (ordinary_head Leanux.WG.modifyDev; refine ordinary_modifyDev _ ?_; intro d; rfl)
    | (ordinary_head Leanux.WG.andM; refine ordinary_andM _ _ ?_ ?_)
    | (ordinary_head Leanux.WG.orM; refine ordinary_orM _ _ ?_ ?_)
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head Functor.discard; refine ordinary_discard ?_)
    | (ordinary_head Functor.map; refine ordinary_map _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_range _ _ _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_forIn _ _ _ ?_)
    | (ordinary_head List.forM; with_reducible refine ordinary_forM _ _ ?_)
    | (ordinary_head ForM.forM; with_reducible refine ordinary_forM _ _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_array _ _ _ ?_)
    | ordinary_head_reduce
    | ordinary_head_match)

theorem setPeerCmd_ordinary (a : PeerAttrs) : OrdinaryAction (Leanux.WG.setPeerCmd a) := by
  unfold Leanux.WG.setPeerCmd
  repeat' first
    | (ordinary_head Leanux.WG.peerRemove; with_reducible exact @peerRemove_ordinary _)
    | (ordinary_head Leanux.WG.sendKeepalive; with_reducible exact @sendKeepalive_ordinary _)
    | (ordinary_head Leanux.WG.sendStagedPackets; with_reducible exact @sendStagedPackets_ordinary _)
    | (ordinary_head Leanux.WG.getDev; refine SameSnapshot.ordinary ?_; with_reducible exact @getDev_sameSnapshot)
    | (ordinary_head Leanux.WG.getPeer; refine SameSnapshot.ordinary ?_; with_reducible exact @getPeer_sameSnapshot _)
    | (ordinary_head Leanux.WG.peerCreate; refine SameSnapshot.ordinary ?_; with_reducible exact @peerCreate_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.peerGet; refine SameSnapshot.ordinary ?_; with_reducible exact @peerGet_sameSnapshot _)
    | (ordinary_head Leanux.WG.peerPut; refine SameSnapshot.ordinary ?_; with_reducible exact @peerPut_sameSnapshot _)
    | (ordinary_head Leanux.WG.pubkeyLookup; refine SameSnapshot.ordinary ?_; with_reducible exact @pubkeyLookup_sameSnapshot _)
    | (ordinary_head Leanux.WG.removeByPeer; refine SameSnapshot.ordinary ?_; with_reducible exact @removeByPeer_sameSnapshot _)
    | (ordinary_head Leanux.WG.setAllowedip; refine SameSnapshot.ordinary ?_; with_reducible exact @setAllowedip_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.setPeerEndpoint; refine SameSnapshot.ordinary ?_; with_reducible exact @setPeerEndpoint_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.setPeer; refine SameSnapshot.ordinary ?_; with_reducible exact @setPeer_sameSnapshot _ _)
    | (ordinary_head Leanux.branch; refine SameSnapshot.ordinary ?_; with_reducible exact @branch_sameSnapshot _ _)
    | (ordinary_head Leanux.branchCmp; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmp_sameSnapshot _ _ _ _)
    | (ordinary_head Leanux.branchCmpExcluded; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmpExcluded_sameSnapshot _ _ _)
    | (ordinary_head Leanux.invariant; refine SameSnapshot.ordinary ?_; with_reducible exact @invariant_sameSnapshot _ _)
    | (ordinary_head Leanux.unsupported; refine SameSnapshot.ordinary ?_; with_reducible exact @unsupported_sameSnapshot _ _)
    | ordinary_strict_step

theorem setPeerCmd_spec (P : Snapshot → Prop) (hp : Stable P) (a : PeerAttrs) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setPeerCmd a
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPeerCmd_ordinary a).wp P hp

theorem wgSetDevice_ordinary (a : DeviceAttrs) : OrdinaryAction (Leanux.WG.wgSetDevice a) := by
  unfold Leanux.WG.wgSetDevice
  repeat' first
    | (ordinary_head Leanux.WG.peerRemoveAll; with_reducible exact @peerRemoveAll_ordinary)
    | (ordinary_head Leanux.WG.peerRemove; with_reducible exact @peerRemove_ordinary _)
    | (ordinary_head Leanux.WG.sendStagedPackets; with_reducible exact @sendStagedPackets_ordinary _)
    | (ordinary_head Leanux.WG.setPeerCmd; with_reducible exact @setPeerCmd_ordinary _)
    | (ordinary_head Leanux.WG.clearPeerEndpointSrc; refine SameSnapshot.ordinary ?_; with_reducible exact @clearPeerEndpointSrc_sameSnapshot _)
    | (ordinary_head Leanux.WG.cookiePrecomputeDeviceKeys; refine SameSnapshot.ordinary ?_; with_reducible exact @cookiePrecomputeDeviceKeys_sameSnapshot)
    | (ordinary_head Leanux.WG.expireCurrentPeerKeypairs; refine SameSnapshot.ordinary ?_; with_reducible exact @expireCurrentPeerKeypairs_sameSnapshot _)
    | (ordinary_head Leanux.WG.generatePublic; refine SameSnapshot.ordinary ?_; with_reducible exact @generatePublic_sameSnapshot _)
    | (ordinary_head Leanux.WG.getDev; refine SameSnapshot.ordinary ?_; with_reducible exact @getDev_sameSnapshot)
    | (ordinary_head Leanux.WG.lookupInterface; refine SameSnapshot.ordinary ?_; with_reducible exact @lookupInterface_sameSnapshot _)
    | (ordinary_head Leanux.WG.peerPut; refine SameSnapshot.ordinary ?_; with_reducible exact @peerPut_sameSnapshot _)
    | (ordinary_head Leanux.WG.precomputeStaticStatic; refine SameSnapshot.ordinary ?_; with_reducible exact @precomputeStaticStatic_sameSnapshot _)
    | (ordinary_head Leanux.WG.pubkeyLookup; refine SameSnapshot.ordinary ?_; with_reducible exact @pubkeyLookup_sameSnapshot _)
    | (ordinary_head Leanux.WG.setPort; refine SameSnapshot.ordinary ?_; with_reducible exact @setPort_sameSnapshot _)
    | (ordinary_head Leanux.WG.setStaticIdentityPrivateKey; refine SameSnapshot.ordinary ?_; with_reducible exact @setStaticIdentityPrivateKey_sameSnapshot _)
    | (ordinary_head Leanux.branch; refine SameSnapshot.ordinary ?_; with_reducible exact @branch_sameSnapshot _ _)
    | (ordinary_head Leanux.branchCmp; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmp_sameSnapshot _ _ _ _)
    | (ordinary_head Leanux.branchCmpExcluded; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmpExcluded_sameSnapshot _ _ _)
    | (ordinary_head Leanux.invariant; refine SameSnapshot.ordinary ?_; with_reducible exact @invariant_sameSnapshot _ _)
    | (ordinary_head Leanux.unsupported; refine SameSnapshot.ordinary ?_; with_reducible exact @unsupported_sameSnapshot _ _)
    | ordinary_strict_step

theorem wgSetDevice_spec (P : Snapshot → Prop) (hp : Stable P) (a : DeviceAttrs) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.wgSetDevice a
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgSetDevice_ordinary a).wp P hp

end Leanux.Spikes.Lifetimes.WGConfig
