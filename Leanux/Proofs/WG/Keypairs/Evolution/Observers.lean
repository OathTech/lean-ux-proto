import Leanux.Proofs.WG.Keypairs.Evolution.Rules
import Leanux.Proofs.Logged.Workers
import Leanux.Proofs.WG.Keypairs.Frames.WGConfig

/-! Evolution through the concrete receive observers. Callbacks retain their
own evolution contracts, so later scheduler composition can supply any checked
placement of receive work. No runner theorem is assumed here. -/
namespace Leanux.Proofs.WG.Keypairs.Observers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.KernelFrames
open Leanux.Proofs.WG.Keypairs.WGFrames Leanux.Proofs.WG.Keypairs.WGTransitions
open Leanux.Proofs.WG.Keypairs.WGMore Leanux.Proofs.WG.Keypairs.WGConfig
open Lean Meta Elab Tactic

set_option maxHeartbeats 300000
set_option pp.structureInstances false

elab "evolves_head " n:ident : tactic => do
  let t := (← getMainTarget).consumeMData
  unless t.isAppOf ``Evolves do throwError "expected Evolves"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do throwError "different action head: {a.getAppFn} versus {name}"

private def evolvesHeadBZ : Nat → Expr → Expr
  | 0, e => e
  | n+1, e =>
    let e := e.consumeMData
    match e with
    | .letE _ _ v b _ => evolvesHeadBZ n (b.instantiate1 v)
    | _ =>
      match e.getAppFn.consumeMData with
      | .letE _ _ v b _ => evolvesHeadBZ n (mkAppN (b.instantiate1 v) e.getAppArgs)
      | .lam .. =>
        let e' := e.headBeta
        if Expr.equal e e' then e else evolvesHeadBZ n e'
      | _ => e

elab "evolves_head_reduce" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``Evolves do throwError "not Evolves"
  let .app f a := t | throwError "missing action"
  let a' := evolvesHeadBZ 64 a
  if Expr.equal a a' then throwError "head unchanged"
  replaceMainGoal [← g.replaceTargetDefEq (.app f a')]

elab "evolves_head_match" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``Evolves do throwError "not Evolves"
  let a := t.getAppArgs.back! |>.consumeMData
  let some _ ← Lean.Meta.matchMatcherApp? a | throwError "not a top matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch g a)


/-- Prove each compiler-generated continuation once, then use its contract. -/
elab "evolves_join_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Evolves do throwError "not Evolves"
  let action := target.getAppArgs.back! |>.consumeMData
  let .letE name ty value body _ := action | throwError "not a let"
  unless name.toString.startsWith "__do_jp" do throwError "not a join continuation"
  let property ← forallTelescope ty fun args _ => do
    let result ← mkAppM ``Evolves #[mkAppN value args]
    mkForallFVars args result
  let valueProof ← mkFreshExprSyntheticOpaqueMVar property
  let (continuation, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun args _ => do
      let result ← mkAppM ``Evolves #[mkAppN f args]
      mkForallFVars args result
    withLocalDeclD `evolves_join contract fun hf => do
      let bodyProp ← mkAppM ``Evolves #[body.instantiate1 f]
      let next ← mkFreshExprSyntheticOpaqueMVar bodyProp
      let proof ← mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (mkApp2 continuation value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "evolves_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Evolves do throwError "not Evolves"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `evolves_join then
      let proof := mkAppN decl.toExpr action.getAppArgs
      try
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
      catch _ => pure ()
  throwError "no continuation contract"

macro "observer_ordinary_leaf" : tactic => `(tactic|
  first
    | (ordinary_head Leanux.hidden; exact (sameSnapshot_of_sameKernel (hidden_sameKernel _)).ordinary)
    | (ordinary_head Leanux.hiddenClock64; exact (hiddenClock64_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.hiddenJiffies; exact (hiddenJiffies_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.recordBudget; exact recordBudget_sameSnapshot.ordinary)
    | (ordinary_head Leanux.budgetExhausted; exact (budgetExhausted_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.recordsLeft; exact recordsLeft_sameSnapshot.ordinary)
    | (ordinary_head Leanux.peekSiteU64; exact (peekSiteU64_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.peekQueuedUnit; exact (peekQueuedUnit_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.branchCmp; exact (branchCmp_sameSnapshot _ _ _ _).ordinary)
    | (ordinary_head Leanux.branch; exact (branch_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.peekHiddenSite; exact peekHiddenSite_sameSnapshot.ordinary)
    | (ordinary_head Leanux.invariant; exact (invariant_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.unsupported; exact (unsupported_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.getDev; exact getDev_sameSnapshot.ordinary)
    | (ordinary_head Leanux.WG.getPeer; exact (getPeer_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.getTxSkb; exact (getTxSkb_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.setTxSkb; exact (setTxSkb_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.WG.freeTxSkb; exact (freeTxSkb_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.getRxSkb; exact (getRxSkb_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.setRxSkb; exact (setRxSkb_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.WG.freeRxSkb; exact (freeRxSkb_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.getKeypair; exact (getKeypair_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.setPeer; exact (setPeer_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.WG.peerGet; exact (peerGet_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.peerPut; exact (peerPut_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.keypairPut; exact keypairPut_ordinary _ _)
    | (ordinary_head Leanux.WG.PrevQueue.peek; exact (PrevQueue_peek_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.decryptPacket; exact (WGMore.decryptPacket_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.endpointFromSkb; exact (endpointFromSkb_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.consumeDataDone; exact consumeDataDone_ordinary _ _ _))

macro "evolves_step" : tactic => `(tactic|
  first
    | contradiction
    | intro_forall
    | with_reducible assumption
    | evolves_join_let
    | evolves_join_use
    | (evolves_head counterLogged; exact counterLogged_evolution _ _)
    | (evolves_head getWorld; exact evolves_getWorld)
    | (evolves_head modifyWorld; refine evolves_modifyWorld _ ?_; intro w; exact Ordinary.refl _)
    | (evolves_head Pure.pure; exact evolves_pure _)
    | (evolves_head MonadExceptOf.throw; exact evolves_throw _)
    | (evolves_head liftM; refine evolves_liftM ?_)
    | (evolves_head StateT.lift; refine evolves_lift ?_)
    | (evolves_head Bind.bind; refine evolves_bind ?_ ?_)
    | (evolves_head ite; refine evolves_ite _ ?_ ?_)
    | (evolves_head Functor.discard; refine evolves_discard ?_)
    | (evolves_head Functor.map; refine evolves_map _ ?_)
    | (evolves_head ForIn.forIn; with_reducible refine evolves_range _ _ _ ?_)
    | (evolves_head ForIn.forIn; with_reducible refine evolves_forIn _ _ _ ?_)
    | (evolves_head ForIn.forIn; with_reducible refine evolves_array _ _ _ ?_)
    | evolves_head_reduce
    | evolves_head_match
    | observer_ordinary_leaf
    | ordinary_strict_step)

theorem workerIterLogged_evolves (worker : Worker) (pid : Option Nat)
    (step afterItem : GhostM Bool) (hs : Evolves step) (ha : Evolves afterItem) :
    Evolves (workerIterLogged worker pid step afterItem) := by
  unfold workerIterLogged
  repeat' evolves_step

theorem workerLoopLogged_evolves (worker : Worker) (pid : Option Nat)
    (step : GhostM Bool) (afterItem : GhostM Unit) (bound : Nat) (drained : String)
    (hs : Evolves step) (ha : Evolves afterItem) :
    Evolves (workerLoopLogged worker pid step afterItem bound drained) := by
  unfold workerLoopLogged
  repeat' first
    | (evolves_head workerIterLogged; refine workerIterLogged_evolves _ _ _ _ hs ?_)
    | evolves_step

theorem runWorkerLogged_evolves (worker : Worker) (body : GhostM Unit)
    (hb : Evolves body) : Evolves (runWorkerLogged worker body) := by
  unfold runWorkerLogged
  repeat' evolves_step

theorem enqueuePerPeerRxLogged_evolves (irq : GhostM Unit) (hi : Evolves irq)
    (id : SkbId) (state : PacketState) : Evolves (enqueuePerPeerRxLogged irq id state) := by
  unfold enqueuePerPeerRxLogged
  repeat' evolves_step

theorem decryptStepLogged_evolves (softirq irq : GhostM Unit)
    (hs : Evolves softirq) (hi : Evolves irq) : Evolves (decryptStepLogged softirq irq) := by
  unfold decryptStepLogged
  repeat' first
    | (evolves_head enqueuePerPeerRxLogged; exact enqueuePerPeerRxLogged_evolves _ hi _ _)
    | evolves_step

theorem decryptIterLogged_evolves (softirq irq : GhostM Unit) (needResched : GhostM Bool)
    (hs : Evolves softirq) (hi : Evolves irq) (hr : Evolves needResched) :
    Evolves (decryptIterLogged softirq irq needResched) := by
  unfold decryptIterLogged
  refine workerIterLogged_evolves _ _ _ _ (decryptStepLogged_evolves _ _ hs hi) ?_
  repeat' evolves_step

theorem groNormalListLogged_evolves
    (callback : List (List UInt8) → GhostM Unit)
    (hc : ∀ packets, Evolves (callback packets)) (gro : GroState) :
    Evolves (groNormalListLogged callback gro) := by
  unfold groNormalListLogged
  repeat' first
    | with_reducible exact hc _
    | evolves_step

theorem groNormalOneLogged_evolves
    (callback : List (List UInt8) → GhostM Unit)
    (hc : ∀ packets, Evolves (callback packets)) (gro : GroState) (pkt : List UInt8) (segs : Nat) :
    Evolves (groNormalOneLogged callback gro pkt segs) := by
  unfold groNormalOneLogged
  repeat' first
    | (evolves_head groNormalListLogged; exact groNormalListLogged_evolves callback hc _)
    | with_reducible exact hc _
    | evolves_step

theorem napiGroReceiveLogged_evolves
    (callback : List (List UInt8) → GhostM Unit)
    (hc : ∀ packets, Evolves (callback packets)) (gro : GroState) (pkt : List UInt8) :
    Evolves (napiGroReceiveLogged callback gro pkt) := by
  unfold napiGroReceiveLogged
  repeat' first
    | (evolves_head groNormalListLogged; exact groNormalListLogged_evolves callback hc _)
    | (evolves_head groNormalOneLogged; exact groNormalOneLogged_evolves callback hc _ _ _)
    | with_reducible exact hc _
    | evolves_step

theorem napiGroFlushAllLogged_evolves
    (callback : List (List UInt8) → GhostM Unit)
    (hc : ∀ packets, Evolves (callback packets)) (gro : GroState) :
    Evolves (napiGroFlushAllLogged callback gro) := by
  unfold napiGroFlushAllLogged
  repeat' first
    | (evolves_head groNormalListLogged; exact groNormalListLogged_evolves callback hc _)
    | (evolves_head groNormalOneLogged; exact groNormalOneLogged_evolves callback hc _ _ _)
    | with_reducible exact hc _
    | evolves_step

theorem rxPollLogged_evolves (pid : PeerId) (budget : Nat)
    (complete : List (List UInt8) → GhostM Unit)
    (hc : ∀ packets, Evolves (complete packets)) :
    Evolves (rxPollLogged pid budget complete) := by
  unfold rxPollLogged
  repeat' first
    | (evolves_head napiGroReceiveLogged; exact napiGroReceiveLogged_evolves complete hc _ _)
    | (evolves_head napiGroFlushAllLogged; exact napiGroFlushAllLogged_evolves complete hc _)
    | with_reducible exact hc _
    | evolves_step

end Leanux.Proofs.WG.Keypairs.Observers
