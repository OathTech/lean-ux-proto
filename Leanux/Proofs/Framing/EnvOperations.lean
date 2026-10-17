import Leanux.Proofs.Framing.EnvLeaves
import Leanux.Proofs.WG.Environment.ObservationSource
import Lean

/-! Original environment contracts over the original 43 store fields.
MTU changes mask precisely the three original device scalars. Routing remains
outside the seven original WireGuard store fields, with its actual effects
and Stops retained by the native adapters. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Lifetimes

def envScalarDevice (d : Device) : Device :=
  { d with mtu := 0, inet4Dev := false, inet6Dev := false }
def envScalarStore (v : ProductStore43) : ProductStore43 :=
  (v.1, v.2.1, v.2.2.1, { v.2.2.2 with dev := v.2.2.2.dev.map envScalarDevice })
def envScalarView (w : World) : ProductStore43 := envScalarStore (productStoreView w)
def envScalarWGView (g : WGWorld) : WGStoreView :=
  { wgStoreView g with dev := g.dev.map envScalarDevice }
abbrev SameEnvScalar (a : Leanux.M α) := SameView envScalarView a

/- Checked composition over the actual product action. Named facts are
selected by their source heads; shared do-continuations receive local contracts. -/
open Lean Meta Elab Tactic in
elab "env_operation_fact " n:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let .app _ action := target | throwError "missing environment action"
  let proof ← Lean.Elab.Term.elabTerm n none
  let (_, _, conclusion) ← forallMetaTelescope (← instantiateMVars (← inferType proof))
  let .app _ framed := (← instantiateMVars conclusion).consumeMData | throwError "missing named action"
  let actualHead := action.consumeMData.headBeta.getAppFn
  let framedHead := framed.consumeMData.headBeta.getAppFn
  let sameHead := match actualHead.constName?, framedHead.constName? with
    | some actual, some expected =>
      actual == expected ||
        ((actual == ``MonadLift.monadLift || actual == ``MonadLiftT.monadLift) &&
          (expected == ``MonadLift.monadLift || expected == ``MonadLiftT.monadLift))
    | _, _ => actualHead == framedHead
  unless sameHead do throwError "different environment action"
  replaceMainGoal (← withReducible (goal.apply proof))

open Lean Meta Elab Tactic in
elab "env_operation_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  if target.isForall then
    evalTactic (← `(tactic| intro))
    return
  let .app property action := target | throwError "missing environment action"
  let action := action.consumeMData
  if let .letE name ty value body _ := action then
    if name.toString.startsWith "__do_jp" then
      let claim ← forallTelescope ty fun args _ =>
        mkForallFVars args (mkApp property (mkAppN value args))
      let proof ← mkFreshExprSyntheticOpaqueMVar claim
      let (continuation, next) ← withLocalDeclD name ty fun f => do
        let claim ← forallTelescope ty fun args _ =>
          mkForallFVars args (mkApp property (mkAppN f args))
        withLocalDeclD `env_join claim fun hf => do
          let next ← mkFreshExprSyntheticOpaqueMVar (mkApp property (body.instantiate1 f))
          return (← mkLambdaFVars #[f, hf] next, next.mvarId!)
      goal.assign (mkApp2 continuation value proof)
      replaceMainGoal [proof.mvarId!, next]
    else
      replaceMainGoal [← goal.replaceTargetDefEq (mkApp property (body.instantiate1 value))]
    return
  if let .letE _ _ value body _ := action.getAppFn.consumeMData then
    replaceMainGoal [← goal.replaceTargetDefEq
      (mkApp property (mkAppN (body.instantiate1 value) action.getAppArgs))]
    return
  let reduced := action.headBeta
  if !Expr.equal action reduced then
    replaceMainGoal [← goal.replaceTargetDefEq (mkApp property reduced)]
    return
  if action.getAppFn.isFVar then
    for decl in ← getLCtx do
      if decl.userName == `env_join then
        let proof := mkAppN decl.toExpr action.getAppArgs
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
    throwError "missing environment continuation contract"
  let head := action.getAppFn.constName?
  if head == some ``Bind.bind then
    evalTactic (← `(tactic| refine SameView.bind ?_ ?_))
  else if head == some ``Pure.pure then
    evalTactic (← `(tactic| exact SameView.pure _ _))
  else if head == some ``ite || head == some ``dite then
    evalTactic (← `(tactic| split))
  else if head == some ``liftM then
    evalTactic (← `(tactic| unfold liftM))
  else if head == some ``StateT.map then
    evalTactic (← `(tactic| apply SameView.map))
  else if (← Lean.Meta.matchMatcherApp? action).isSome then
    replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)
  else
    throwError "unhandled environment action head {head}"

macro "env_operation_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
  let mut use ← `(tactic| fail "no named environment fact")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | env_operation_fact $fact | ($use:tactic))
  let expand ← if fs.getElems.isEmpty then `(tactic| skip) else `(tactic| unfold $fs:ident*)
  `(tactic| ($expand:tactic; repeat' first | ($use:tactic) | env_operation_step))

theorem modifyDev_envScalar_spec (P : ProductStore43 → Prop) (f : Device → Device)
    (hf : ∀ d, envScalarDevice (f d) = envScalarDevice d) :
    Hoare (MonadLift.monadLift (modifyDev f) : Leanux.M Unit)
      (fun w => P (envScalarView w)) (fun _ w => P (envScalarView w)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hp hr
  cases hr
  simpa [envScalarView, envScalarStore, productStoreView, wgStoreView, modifyDev,
    liftWG, Option.map_map, Function.comp_def, hf] using hp

theorem wgSetMtu_sameEnvScalar (mtu : Int) :
    SameEnvScalar (MonadLift.monadLift (WG.setMtu mtu) : Leanux.M Int) := by
  have h : SameView envScalarWGView (WG.setMtu mtu) := by
    unfold WG.setMtu
    split
    · exact SameView.pure _ _
    · split
      · exact SameView.pure _ _
      · apply SameView.bind
        · intro initial
          apply hoare_modify
          intro g hg
          cases hd : g.dev <;>
            simpa [envScalarWGView, wgStoreView, envScalarDevice, hd] using hg
        · intro _
          exact SameView.pure _ _
  apply sameView_liftWG envScalarView envScalarWGView (WG.setMtu mtu) h
  intro w g ambient hg
  change (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter),
    envScalarWGView g) = (_, _, _, envScalarWGView w.wg)
  rw [hg]
  rfl

theorem setMtu_sameEnvScalar (mtu : Nat) : SameEnvScalar (Env.setMtu mtu) := by
  have ha {α : Type} (a : AmbientM α) : SameEnvScalar (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => envScalarView w = k) (fun _ _ h => h)
  have hg : SameEnvScalar getWG := fun k => productGetWG_spec (fun s => envScalarStore s = k)
  have hd : SameEnvScalar (monadLift getDev : Leanux.M Device) :=
    fun k => productGetDev_spec (fun s => envScalarStore s = k)
  have hr {α : Type} (a : Net.M α) :
      SameEnvScalar (monadLift a : Leanux.M α) :=
    fun k => productRouting_spec a (fun s => envScalarStore s = k)
  have routing : SameEnvScalar (getRouting : Leanux.M Net.Routing) :=
    hr ((fun (r : Net.State) => r.toRouting) <$> (get : Net.M Net.State))
  have editRouting (f : Net.Routing → Net.Routing) :
      SameEnvScalar (modifyRouting f : Leanux.M Unit) :=
    hr (modify (fun (r : Net.State) => {r with toRouting := f r.toRouting}) : Net.M Unit)
  have hl {α β : Type} (xs : List α) (init : β)
      (f : α → β → Leanux.M (ForInStep β))
      (hf : ∀ x b, SameEnvScalar (f x b)) : SameEnvScalar (forIn xs init f) :=
    fun k => list_view_spec envScalarView (fun s => s = k) xs init f (fun x b => hf x b k)
  have hm (n : Int) : SameEnvScalar (monadLift (WG.setMtu n) : Leanux.M Int) := wgSetMtu_sameEnvScalar n
  env_operation_source [Env.setMtu, Env.inetdevDestroy, skipCut, unsupported]
    using [hg, hd, hr, routing, editRouting, hm, ha, hl]

theorem senderSource_sameKernel (family dest tos : Nat) (ll : Bool) :
    SameProductStore (Env.senderSource family dest tos ll) := by
  have ha {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => productStoreView w = k) (fun _ _ h => h)
  have hr {α : Type} (a : Net.M α) :
      SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productRouting_spec a (fun s => s = k)
  have routing : SameProductStore (getRouting : Leanux.M Net.Routing) :=
    hr ((fun (r : Net.State) => r.toRouting) <$> (get : Net.M Net.State))
  env_operation_source [Env.senderSource, unsupported] using [routing, ha]

theorem routeIntoWg0_sameKernel : SameProductStore Env.routeIntoWg0 := by
  have ha {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => productStoreView w = k) (fun _ _ h => h)
  have hd : SameProductStore (monadLift getDev : Leanux.M Device) :=
    fun k => productGetDev_spec (fun s => s = k)
  have hr {α : Type} (a : Net.M α) :
      SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productRouting_spec a (fun s => s = k)
  have routing : SameProductStore (getRouting : Leanux.M Net.Routing) :=
    hr ((fun (r : Net.State) => r.toRouting) <$> (get : Net.M Net.State))
  have editRouting (f : Net.Routing → Net.Routing) :
      SameProductStore (modifyRouting f : Leanux.M Unit) :=
    hr (modify (fun (r : Net.State) => {r with toRouting := f r.toRouting}) : Net.M Unit)
  have fixture : SameProductStore getEnv := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  have editFixture (f : EnvWorld → EnvWorld) : SameProductStore (modifyEnv f) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  env_operation_source [Env.routeIntoWg0, Env.outsideWindow, getAmbient, modifyAmbient]
    using [fixture, hd, hr, routing, editRouting, editFixture, ha]

theorem wgDeladdr_sameKernel (family : Nat) : SameProductStore (Env.wgDeladdr family) := by
  have ha {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => productStoreView w = k) (fun _ _ h => h)
  have hg : SameProductStore getWG := fun k => productGetWG_spec (fun s => s = k)
  have hr {α : Type} (a : Net.M α) :
      SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productRouting_spec a (fun s => s = k)
  have routing : SameProductStore (getRouting : Leanux.M Net.Routing) :=
    hr ((fun (r : Net.State) => r.toRouting) <$> (get : Net.M Net.State))
  have editRouting (f : Net.Routing → Net.Routing) :
      SameProductStore (modifyRouting f : Leanux.M Unit) :=
    hr (modify (fun (r : Net.State) => {r with toRouting := f r.toRouting}) : Net.M Unit)
  env_operation_source [Env.wgDeladdr, unsupported]
    using [hg, hr, routing, editRouting, ha]

theorem wgDelroute_sameKernel (family : Nat) :
    SameProductStore (Env.wgDelroute family false 0 0 0 0 0) := by
  have ha {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => productStoreView w = k) (fun _ _ h => h)
  have hg : SameProductStore getWG := fun k => productGetWG_spec (fun s => s = k)
  have hr {α : Type} (a : Net.M α) :
      SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productRouting_spec a (fun s => s = k)
  have routing : SameProductStore (getRouting : Leanux.M Net.Routing) :=
    hr ((fun (r : Net.State) => r.toRouting) <$> (get : Net.M Net.State))
  have editRouting (f : Net.Routing → Net.Routing) :
      SameProductStore (modifyRouting f : Leanux.M Unit) :=
    hr (modify (fun (r : Net.State) => {r with toRouting := f r.toRouting}) : Net.M Unit)
  env_operation_source [Env.wgDelroute, unsupported]
    using [hg, hr, routing, editRouting, ha]

theorem xmitPacket_sameKernel (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) :
    SameProductStore (Env.xmitPacket family addr payload mtu tos) := by
  have ha {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => productStoreView w = k) (fun _ _ h => h)
  env_operation_source [Env.xmitPacket, invariant, unsupported] using [ha]

theorem xmitPackets_sameKernel (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    SameProductStore (Env.xmitPackets family addr payload opts) := by
  have ha {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => productStoreView w = k) (fun _ _ h => h)
  have hd : SameProductStore (monadLift getDev : Leanux.M Device) :=
    fun k => productGetDev_spec (fun s => s = k)
  have fixture : SameProductStore getEnv := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  have packet := xmitPacket_sameKernel
  env_operation_source [Env.xmitPackets, unsupported] using [hd, fixture, packet, ha]

theorem observeTail_sameKernel : SameProductStore Leanux.Proofs.WG.Environment.observeTail := by
  have ha {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => productStoreView w = k) (fun _ _ h => h)
  have hg : SameProductStore getWG := fun k => productGetWG_spec (fun s => s = k)
  have hr {α : Type} (a : Net.M α) :
      SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productRouting_spec a (fun s => s = k)
  have routing : SameProductStore (getRouting : Leanux.M Net.Routing) :=
    hr ((fun (r : Net.State) => r.toRouting) <$> (get : Net.M Net.State))
  have fixture : SameProductStore getEnv := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  have editFixture (f : EnvWorld → EnvWorld) : SameProductStore (modifyEnv f) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  have crypt := requireNoCryptWork_sameKernel
  have sent := deliverSent_sameKernel
  env_operation_source [Leanux.Proofs.WG.Environment.observeTail, unsupported]
    using [hg, routing, fixture, editFixture, crypt, sent, ha]

end Leanux.Proofs.Framing
