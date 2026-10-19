import Leanux.Proofs.Framing.BatchRefills
import Leanux.Proofs.WG.AllowedIps.RoutingSchedulerFrames
import Leanux.Proofs.WG.AllowedIps.RoutingNapiFrames
import Leanux.Proofs.Framing.EnvLeaves
import Leanux.Proofs.WG.Keypairs.Frames.Env

/-! Deferred environment workers retain routing at every normal endpoint.
The captured work queues do not imply residency: original getters establish
fresh setter facts or Stop, and worker cleanup may delete resident peers. The
legacy environment import shares generated matcher declarations under Lean 4.35. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

open Lean Meta Elab Tactic

private def routingWorkerAction (target : Expr) : MetaM Expr := do
  unless target.isAppOf ``Preserves && target.getAppArgs.size ≥ 2 do
    throwError "not a preservation contract"
  return target.getAppArgs.back!.consumeMData

elab "routing_worker_head " name:ident : tactic => withMainContext do
  let action ← routingWorkerAction (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  let rec head (fuel : Nat) (e : Expr) : Name :=
    match fuel with
    | 0 => .anonymous
    | n+1 =>
      let e := e.consumeMData
      if e.isAppOf ``MonadLift.monadLift || e.isAppOf ``MonadLiftT.monadLift || e.isAppOf ``liftM then
        if e.getAppArgs.isEmpty then .anonymous else head n e.getAppArgs.back!
      else
        match e.getAppFn with
        | .const name _ => name
        | _ => .anonymous
  let actual := head 4 action
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different preservation action"

elab "routing_worker_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let action ← routingWorkerAction target
  let rec reduce : Nat → Expr → Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else reduce n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e
          else reduce n (mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Expr.equal e next then e else reduce n next
        | _ => e
  let next := reduce 64 action
  if Expr.equal action next then throwError "head unchanged"
  replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn
    (target.getAppArgs.set! (target.getAppArgs.size - 1) next))]

elab "routing_worker_match" : tactic => withMainContext do
  let goal ← getMainGoal
  let action ← routingWorkerAction (← instantiateMVars (← goal.getType)).consumeMData
  let some _ ← matchMatcherApp? action | throwError "not a head matcher"
  replaceMainGoal (← Split.splitMatch goal action)

elab "routing_worker_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let action ← routingWorkerAction target
  let .letE name ty value body _ := action | throwError "not a shared continuation"
  unless name.toString.startsWith "__do_jp" do throwError "not a shared continuation"
  let pred := target.getAppArgs[target.getAppArgs.size - 2]!
  let property := fun a => mkAppM ``Preserves #[pred, a]
  let contract ← forallTelescope ty fun xs _ => do
    mkForallFVars xs (← property (mkAppN value xs))
  let valueProof ← mkFreshExprSyntheticOpaqueMVar contract
  let (proof, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun xs _ => do
      mkForallFVars xs (← property (mkAppN f xs))
    withLocalDeclD `routing_worker_continuation contract fun hf => do
      let next ← mkFreshExprSyntheticOpaqueMVar (← property (body.instantiate1 f))
      pure (← mkLambdaFVars #[f, hf] next, next.mvarId!)
  goal.assign (mkApp2 proof value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "routing_worker_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let action ← routingWorkerAction target
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `routing_worker_continuation then
      let proof := mkAppN decl.toExpr action.getAppArgs
      if ← withReducible (isDefEq (← inferType proof) target) then
        goal.assign proof
        replaceMainGoal []
        return
  throwError "no continuation contract"

/-- Preserve the complete native pre/post relation through the actual adapter. -/
private theorem native_lift_spec (a : WG.M α) {P : WGWorld → Prop}
    {Q : α → WGWorld → Prop} (ha : Hoare a P Q) :
    Hoare (MonadLift.monadLift a : Leanux.M α)
      (fun w => P w.wg) (fun x w => Q x w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hp hr
  change (liftWG a).run w = .ok (x, v) at hr
  rw [liftWG_run] at hr
  cases he : (a.run w.wg).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y, g⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact (hoare_iff_run_ambient _ _ _).mp ha _ _ _ _ _ hp he

theorem deliverSent_routing : SameView (fun w : World => routingView w.wg) Env.deliverSent :=
  deliverSent_sameKernel.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w => routingView w.wg) (fun _ => rfl)

theorem requireNoCryptWork_routing : SameView (fun w : World => routingView w.wg) Env.requireNoCryptWork :=
  requireNoCryptWork_sameKernel.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w => routingView w.wg) (fun _ => rfl)

theorem requireDrained_routing (what : String) (queues : List Bool) :
    SameView (fun w : World => routingView w.wg) (Env.requireDrained what queues) :=
  (requireDrained_sameKernel what queues).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w => routingView w.wg) (fun _ => rfl)

theorem runCryptWorkers_routing : ProductRetainsRoutingCall Env.runCryptWorkers := by
  intro s
  have hs := RetainsRoutingCall.wp (schedule_routing none) s
  have hd := deliverSent_routing.wp (RetainsRouting s)
  have main : Preserves (fun w : World => RetainsRouting s (routingView w.wg)) Env.runCryptWorkers := by
    unfold Env.runCryptWorkers
    exact preserves_bind hs (fun _ => hd)
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem runOneSendWorker_routing : ProductRetainsRoutingCall Env.runOneSendWorker := by
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have hm (pid : PeerId) := native_lift_spec _
    ((modifyDev_routing (fun d => { d with sendWorkQueue := d.sendWorkQueue.erase pid })
      (fun _ => rfl)).wp P)
  have hw (pid : PeerId) := RetainsRoutingCall.wp
    (runWorker_routing .sendWorker _ (handshakeSendWorker_routing pid).liftWG) s
  let R (pid : PeerId) (p : Peer) (w : World) :=
    P (routingView w.wg) ∧
      (w.wg.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList
  let tail (pid : PeerId) (p : Peer) : Leanux.M Unit := do
    let d ← getDev
    setPeer pid { p with handshakePending := d.sendWorkQueue.contains pid }
    Env.runWorker .sendWorker (handshakeSendWorker pid)
  have tailSpec (pid : PeerId) (p : Peer) :
      Hoare (tail pid p) (R pid p) (fun _ w => P (routingView w.wg)) := by
    have hd := productGetDev_spec (fun store =>
      P (store.2.2.2.dev.map routingState) ∧
      (store.2.2.2.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList)
    unfold tail
    apply hoare_bind _ _ hd
    intro d
    exact hoare_bind _ _ (native_lift_spec _
      (routing_setPeer P pid { p with handshakePending := d.sendWorkQueue.contains pid }))
      (fun _ => hw pid)
  have selected (pid : PeerId) : Preserves (fun w : World => P (routingView w.wg)) (do
      modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}
      let p ← getPeer pid
      if !p.handshakePending then invariant "queued work without a pending flag"
      tail pid p : Leanux.M Unit) := by
    apply preserves_bind (hm pid)
    intro _
    apply hoare_bind _ _ (native_lift_spec _ (routing_getPeer P pid))
    intro p
    split
    · have bad : Hoare (invariant "queued work without a pending flag" : Leanux.M Unit)
          (R pid p) (fun _ _ => False) := by
        apply (hoare_iff_run _ _ _).mpr
        intro w x v hi hr
        cases hr
      apply hoare_bind _ _ bad
      intro _
      exact hoare_consequence (tailSpec pid p) (fun _ h => False.elim h) (fun _ _ h => h)
    · exact tailSpec pid p
  have main : Preserves (fun w : World => P (routingView w.wg)) Env.runOneSendWorker := by
    unfold Env.runOneSendWorker
    apply preserves_bind dev
    intro d
    cases d.sendWorkQueue.head? with
    | none => exact ambient (AmbientM.invariant _)
    | some headPid =>
      apply preserves_bind (ambient (AmbientM.peekUnit .sendWorker))
      intro unit
      cases unit with
      | none => exact preserves_bind (preserves_pure headPid) (fun pid => selected pid)
      | some u =>
        exact preserves_bind (ambient (AmbientM.resolveUnit .sendWorker u d.sendWorkQueue))
          (fun pid => selected pid)

  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem runOneClearWorker_routing : ProductRetainsRoutingCall Env.runOneClearWorker := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) Env.runOneClearWorker := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w => P (routingView w.wg)) no) :
        Preserves (fun w => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w => P (routingView w.wg)) (body i b)) :
        Preserves (fun w => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have hm (pid : PeerId) := native_lift_spec _
      ((modifyDev_routing (fun d => { d with clearWorkQueue := d.clearWorkQueue.erase pid })
        (fun _ => rfl)).wp P)
    have hw (pid : PeerId) := RetainsRoutingCall.wp
      (runWorker_routing .clearPeerWorker _ (queuedExpiredZeroKeyMaterial_routing pid).liftWG) s
    unfold Env.runOneClearWorker
    repeat' first
      | (routing_worker_head modifyDev; exact hm _)
      | (routing_worker_head Env.runWorker; exact hw _)
      | routing_worker_join
      | routing_worker_join_use
      | (routing_worker_head getWG; exact readWG)
      | (routing_worker_head getDev; exact dev)
      | (routing_worker_head modifyWG; exact edit _ (fun _ => rfl))
      | (routing_worker_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (routing_worker_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (routing_worker_head invariant; exact ambient (AmbientM.invariant _))
      | (routing_worker_head unsupported; exact ambient (AmbientM.unsupported _))
      | (routing_worker_head recordBudget; exact ambient AmbientM.recordBudget)
      | (routing_worker_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (routing_worker_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (routing_worker_head resolveUnit; exact ambient (AmbientM.resolveUnit _ _ _))
      | (routing_worker_head budgetExhausted; exact ambient (AmbientM.budgetExhausted _))
      | (routing_worker_head Functor.discard; apply discard_view_spec (fun w : World => routingView w.wg) P)
      | (routing_worker_head MonadExceptOf.throw; exact hoare_throw _)
      | (routing_worker_head Pure.pure; exact preserves_pure _)
      | (routing_worker_head Bind.bind; apply preserves_bind)
      | (routing_worker_head ForIn.forIn; apply loop)
      | (routing_worker_head ite; apply choose)
      | maintenance_intro
      | routing_worker_reduce
      | routing_worker_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem runSendWorkers_routing : ProductRetainsRoutingCall Env.runSendWorkers := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) Env.runSendWorkers := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w => P (routingView w.wg)) no) :
        Preserves (fun w => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w => P (routingView w.wg)) (body i b)) :
        Preserves (fun w => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have noCrypt := requireNoCryptWork_routing.wp P
    have deliver := deliverSent_routing.wp P
    have worker := RetainsRoutingCall.wp runOneSendWorker_routing s
    have schedule := RetainsRoutingCall.wp (schedule_routing none) s
    unfold Env.runSendWorkers
    repeat' first
      | (routing_worker_head Env.requireNoCryptWork; exact noCrypt)
      | (routing_worker_head Env.deliverSent; exact deliver)
      | (routing_worker_head Env.runOneSendWorker; exact worker)
      | (routing_worker_head Env.schedule; exact schedule)
      | routing_worker_join
      | routing_worker_join_use
      | (routing_worker_head getWG; exact readWG)
      | (routing_worker_head getDev; exact dev)
      | (routing_worker_head modifyWG; exact edit _ (fun _ => rfl))
      | (routing_worker_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (routing_worker_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (routing_worker_head invariant; exact ambient (AmbientM.invariant _))
      | (routing_worker_head unsupported; exact ambient (AmbientM.unsupported _))
      | (routing_worker_head recordBudget; exact ambient AmbientM.recordBudget)
      | (routing_worker_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (routing_worker_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (routing_worker_head resolveUnit; exact ambient (AmbientM.resolveUnit _ _ _))
      | (routing_worker_head budgetExhausted; exact ambient (AmbientM.budgetExhausted _))
      | (routing_worker_head Functor.discard; apply discard_view_spec (fun w : World => routingView w.wg) P)
      | (routing_worker_head MonadExceptOf.throw; exact hoare_throw _)
      | (routing_worker_head Pure.pure; exact preserves_pure _)
      | (routing_worker_head Bind.bind; apply preserves_bind)
      | (routing_worker_head ForIn.forIn; apply loop)
      | (routing_worker_head ite; apply choose)
      | maintenance_intro
      | routing_worker_reduce
      | routing_worker_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem afterXmit_routing : ProductRetainsRoutingCall Env.afterXmit := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) Env.afterXmit := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w => P (routingView w.wg)) no) :
        Preserves (fun w => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w => P (routingView w.wg)) (body i b)) :
        Preserves (fun w => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have crypt := RetainsRoutingCall.wp runCryptWorkers_routing s
    have send := RetainsRoutingCall.wp runSendWorkers_routing s
    have drained (what : String) (queues : List Bool) := (requireDrained_routing what queues).wp P
    unfold Env.afterXmit
    repeat' first
      | (routing_worker_head Env.runCryptWorkers; exact crypt)
      | (routing_worker_head Env.runSendWorkers; exact send)
      | (routing_worker_head Env.requireDrained; exact drained _ _)
      | routing_worker_join
      | routing_worker_join_use
      | (routing_worker_head getWG; exact readWG)
      | (routing_worker_head getDev; exact dev)
      | (routing_worker_head modifyWG; exact edit _ (fun _ => rfl))
      | (routing_worker_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (routing_worker_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (routing_worker_head invariant; exact ambient (AmbientM.invariant _))
      | (routing_worker_head unsupported; exact ambient (AmbientM.unsupported _))
      | (routing_worker_head recordBudget; exact ambient AmbientM.recordBudget)
      | (routing_worker_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (routing_worker_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (routing_worker_head resolveUnit; exact ambient (AmbientM.resolveUnit _ _ _))
      | (routing_worker_head budgetExhausted; exact ambient (AmbientM.budgetExhausted _))
      | (routing_worker_head Functor.discard; apply discard_view_spec (fun w : World => routingView w.wg) P)
      | (routing_worker_head MonadExceptOf.throw; exact hoare_throw _)
      | (routing_worker_head Pure.pure; exact preserves_pure _)
      | (routing_worker_head Bind.bind; apply preserves_bind)
      | (routing_worker_head ForIn.forIn; apply loop)
      | (routing_worker_head ite; apply choose)
      | maintenance_intro
      | routing_worker_reduce
      | routing_worker_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.AllowedIps
