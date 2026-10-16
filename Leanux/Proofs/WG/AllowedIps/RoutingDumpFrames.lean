import Leanux.Proofs.WG.AllowedIps.RoutingEnvControlsCompletion
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! Stepped and whole netlink dumps retain routing at normal endpoints. Their
actual cursor acquisition/release can retire peers; no cursor-validity or
successful-drain premise is required. Socket/serialization frames retain the
complete routing projection, and all original Stops remain observable. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.NetlinkDump Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false


/-- The original arbitrary product action retains its complete dump mask. -/
theorem dumpKernel_routing (a : Leanux.M α) (ha : SameView productDumpView a) :
    SameView (fun w : World => routingView w.wg) a :=
  ha.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)

theorem dump_routing_native (a : WG.M α) (ha : SameDump a) : SameView routingView a :=
  ha.of_factor (fun k : WGStoreView => k.dev.map routingState) routingView (fun _ => rfl)

elab "routing_endpoint_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Preserves do Lean.throwError "not a preservation contract"
  let .app front action := target | Lean.throwError "missing action"
  let rec reduce : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else reduce n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .lam .. =>
          let next := e.headBeta
          if Lean.Expr.equal e next then e else reduce n next
        | _ => e
  let action' := reduce 64 action
  let action' ←
    if (← Lean.Meta.matchMatcherApp? action').isSome then
      match ← Lean.Meta.reduceMatcher? action' with
      | .reduced next => pure next
      | _ => pure action'
    else pure action'
  if Lean.Expr.equal action action' then Lean.throwError "head unchanged"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp front action')]

elab "routing_endpoint_join" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Preserves do Lean.throwError "not a preservation contract"
  let .app front action := target | Lean.throwError "missing action"
  let .letE name ty value body _ := action.consumeMData | Lean.throwError "not a let"
  unless name.toString.startsWith "__do_jp" do Lean.throwError "not a join"
  let property (a : Lean.Expr) := Lean.mkApp front a
  let valueContract ← Lean.Meta.forallTelescope ty fun args _ => do
    Lean.Meta.mkForallFVars args (property (Lean.mkAppN value args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar valueContract
  let (continuation, next) ← Lean.Meta.withLocalDeclD name ty fun fn => do
    let contract ← Lean.Meta.forallTelescope ty fun args _ => do
      Lean.Meta.mkForallFVars args (property (Lean.mkAppN fn args))
    Lean.Meta.withLocalDeclD `routing_preserves_join contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 fn))
      let proof ← Lean.Meta.mkLambdaFVars #[fn, hf] next
      pure (proof, next.mvarId!)
  goal.assign (Lean.mkApp2 continuation value valueProof)
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "routing_endpoint_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Preserves do Lean.throwError "not a preservation contract"
  let action := target.getAppArgs.back!.consumeMData
  unless action.getAppFn.isFVar do Lean.throwError "not a local continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `routing_preserves_join then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "missing continuation contract"

theorem wgGetDeviceDone_routing (ctx : DumpCtx) : RetainsRoutingCall (wgGetDeviceDone ctx) := by
  intro s
  have hp : Preserves (fun w : WGWorld => RetainsRouting s (routingView w)) (wgGetDeviceDone ctx) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : WGWorld => RetainsRouting s (routingView w))
          (MonadLift.monadLift a : WG.M α) := hoare_liftAmbient a _
    unfold wgGetDeviceDone
    repeat' first
      | (control_endpoint_head peerPut; exact RetainsRoutingCall.wp (peerPut_retainsRouting _) s)
      | (control_endpoint_head branch; exact ambient _)
      | (control_endpoint_head invariant; exact ambient _)
      | (control_endpoint_head unsupported; exact ambient _)
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (control_endpoint_head WG.andM; unfold WG.andM)
      | (control_endpoint_head WG.orM; unfold WG.orM)
      | routing_endpoint_join
      | routing_endpoint_join_use
      | routing_endpoint_reduce
      | maintenance_intro
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

theorem deviceDumpTail_routing (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    RetainsRoutingCall (deviceDumpTailSource d ctx skb flags attrs) := by
  intro s
  have hp : Preserves (fun w : WGWorld => RetainsRouting s (routingView w)) (deviceDumpTailSource d ctx skb flags attrs) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : WGWorld => RetainsRouting s (routingView w))
          (MonadLift.monadLift a : WG.M α) := hoare_liftAmbient a _
    have loop {α β : Type} (xs : List α) (init : β)
        (f : α → β → WG.M (ForInStep β))
        (hf : ∀ x b, Preserves (fun w => RetainsRouting s (routingView w)) (f x b)) :
        Preserves (fun w => RetainsRouting s (routingView w)) (forIn xs init f) :=
      list_view_spec routingView (RetainsRouting s) xs init f hf
    unfold deviceDumpTailSource
    repeat' first
      | (control_endpoint_head getPeer; exact (getPeer_routing _).wp (RetainsRouting s))
      | (control_endpoint_head requireNotPending; exact (requireNotPending_routing _ _).wp (RetainsRouting s))
      | (control_endpoint_head getPeerDump; exact ((getPeerDump_sameWGWorld _ _ _).factor routingView).wp (RetainsRouting s))
      | (control_endpoint_head peerGet; exact (peerGet_routing _).wp (RetainsRouting s))
      | (control_endpoint_head peerPut; exact RetainsRoutingCall.wp (peerPut_retainsRouting _) s)
      | (control_endpoint_head ForIn.forIn; first | apply loop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
      | (control_endpoint_head branch; exact ambient _)
      | (control_endpoint_head invariant; exact ambient _)
      | (control_endpoint_head unsupported; exact ambient _)
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (control_endpoint_head WG.andM; unfold WG.andM)
      | (control_endpoint_head WG.orM; unfold WG.orM)
      | routing_endpoint_join
      | routing_endpoint_join_use
      | routing_endpoint_reduce
      | maintenance_intro
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

theorem wgGetDeviceDump_routing (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    RetainsRoutingCall (wgGetDeviceDump ctx prevSeq skb) := by
  intro s
  have hp : Preserves (fun w : WGWorld => RetainsRouting s (routingView w)) (wgGetDeviceDump ctx prevSeq skb) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : WGWorld => RetainsRouting s (routingView w))
          (MonadLift.monadLift a : WG.M α) := hoare_liftAmbient a _
    rw [wgGetDeviceDump_source]
    repeat' first
      | (control_endpoint_head getDev; exact (routing_kernel (project := id) _ getDev_sameWGStore).wp (RetainsRouting s))
      | (control_endpoint_head deviceDumpHeaderSource; exact (routing_kernel (project := id) _ (deviceDumpHeader_sameWGStore _ _ _ _)).wp (RetainsRouting s))
      | (control_endpoint_head deviceDumpTailSource; exact RetainsRoutingCall.wp (deviceDumpTail_routing _ _ _ _ _) s)
      | (control_endpoint_head branch; exact ambient _)
      | (control_endpoint_head invariant; exact ambient _)
      | (control_endpoint_head unsupported; exact ambient _)
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (control_endpoint_head WG.andM; unfold WG.andM)
      | (control_endpoint_head WG.orM; unfold WG.orM)
      | routing_endpoint_join
      | routing_endpoint_join_use
      | routing_endpoint_reduce
      | maintenance_intro
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

theorem netlinkDump_routing (fd : Nat) : RetainsRoutingCall (netlinkDump fd) := by
  intro s
  have hp : Preserves (fun w : WGWorld => RetainsRouting s (routingView w)) (netlinkDump fd) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : WGWorld => RetainsRouting s (routingView w))
          (MonadLift.monadLift a : WG.M α) := hoare_liftAmbient a _
    unfold netlinkDump
    repeat' first
      | (control_endpoint_head getNlSock; exact ((getNlSock_sameWGWorld _).factor routingView).wp (RetainsRouting s))
      | (control_endpoint_head setNlSock; exact (dump_routing_native _ (setNlSock_sameDump _ _)).wp (RetainsRouting s))
      | (control_endpoint_head wgGetDeviceDump; exact RetainsRoutingCall.wp (wgGetDeviceDump_routing _ _ _) s)
      | (control_endpoint_head wgGetDeviceDone; exact RetainsRoutingCall.wp (wgGetDeviceDone_routing _) s)
      | (control_endpoint_head branch; exact ambient _)
      | (control_endpoint_head invariant; exact ambient _)
      | (control_endpoint_head unsupported; exact ambient _)
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (control_endpoint_head WG.andM; unfold WG.andM)
      | (control_endpoint_head WG.orM; unfold WG.orM)
      | routing_endpoint_join
      | routing_endpoint_join_use
      | routing_endpoint_reduce
      | maintenance_intro
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

theorem netlinkDumpStart_routing (fd : Nat) (ref : DeviceRef) :
    RetainsRoutingCall (netlinkDumpStart fd ref) := by
  intro s
  have hp : Preserves (fun w : WGWorld => RetainsRouting s (routingView w)) (netlinkDumpStart fd ref) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : WGWorld => RetainsRouting s (routingView w))
          (MonadLift.monadLift a : WG.M α) := hoare_liftAmbient a _
    unfold netlinkDumpStart
    repeat' first
      | (control_endpoint_head getNlSock; exact ((getNlSock_sameWGWorld _).factor routingView).wp (RetainsRouting s))
      | (control_endpoint_head setNlSock; exact (dump_routing_native _ (setNlSock_sameDump _ _)).wp (RetainsRouting s))
      | (control_endpoint_head lookupInterface; exact ((lookupInterface_sameWGWorld _).factor routingView).wp (RetainsRouting s))
      | (control_endpoint_head netlinkDump; exact RetainsRoutingCall.wp (netlinkDump_routing _) s)
      | (control_endpoint_head branch; exact ambient _)
      | (control_endpoint_head invariant; exact ambient _)
      | (control_endpoint_head unsupported; exact ambient _)
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (control_endpoint_head WG.andM; unfold WG.andM)
      | (control_endpoint_head WG.orM; unfold WG.orM)
      | routing_endpoint_join
      | routing_endpoint_join_use
      | routing_endpoint_reduce
      | maintenance_intro
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

theorem netlinkRecvmsg_routing (fd : Nat) : RetainsRoutingCall (netlinkRecvmsg fd) := by
  intro s
  have hp : Preserves (fun w : WGWorld => RetainsRouting s (routingView w)) (netlinkRecvmsg fd) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : WGWorld => RetainsRouting s (routingView w))
          (MonadLift.monadLift a : WG.M α) := hoare_liftAmbient a _
    unfold netlinkRecvmsg
    repeat' first
      | (control_endpoint_head getNlSock; exact ((getNlSock_sameWGWorld _).factor routingView).wp (RetainsRouting s))
      | (control_endpoint_head setNlSock; exact (dump_routing_native _ (setNlSock_sameDump _ _)).wp (RetainsRouting s))
      | (control_endpoint_head netlinkDump; exact RetainsRoutingCall.wp (netlinkDump_routing _) s)
      | (control_endpoint_head branch; exact ambient _)
      | (control_endpoint_head invariant; exact ambient _)
      | (control_endpoint_head unsupported; exact ambient _)
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (control_endpoint_head WG.andM; unfold WG.andM)
      | (control_endpoint_head WG.orM; unfold WG.orM)
      | routing_endpoint_join
      | routing_endpoint_join_use
      | routing_endpoint_reduce
      | maintenance_intro
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

theorem wgGetDevice_routing (ref : DeviceRef) : RetainsRoutingCall (wgGetDevice ref) := by
  intro s
  have hp : Preserves (fun w : WGWorld => RetainsRouting s (routingView w)) (wgGetDevice ref) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : WGWorld => RetainsRouting s (routingView w))
          (MonadLift.monadLift a : WG.M α) := hoare_liftAmbient a _
    have loop {α β : Type} (xs : List α) (init : β)
        (f : α → β → WG.M (ForInStep β))
        (hf : ∀ x b, Preserves (fun w => RetainsRouting s (routingView w)) (f x b)) :
        Preserves (fun w => RetainsRouting s (routingView w)) (forIn xs init f) :=
      list_view_spec routingView (RetainsRouting s) xs init f hf
    unfold wgGetDevice
    repeat' first
      | (control_endpoint_head netlinkDumpStart; exact RetainsRoutingCall.wp (netlinkDumpStart_routing _ _) s)
      | (control_endpoint_head netlinkRecvmsg; exact RetainsRoutingCall.wp (netlinkRecvmsg_routing _) s)
      | (control_endpoint_head coalesce; exact ((coalesce_sameWGWorld _).factor routingView).wp (RetainsRouting s))
      | (control_endpoint_head ForIn.forIn; first | apply loop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
      | (control_endpoint_head branch; exact ambient _)
      | (control_endpoint_head invariant; exact ambient _)
      | (control_endpoint_head unsupported; exact ambient _)
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (control_endpoint_head WG.andM; unfold WG.andM)
      | (control_endpoint_head WG.orM; unfold WG.orM)
      | routing_endpoint_join
      | routing_endpoint_join_use
      | routing_endpoint_reduce
      | maintenance_intro
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)


end Leanux.Proofs.WG.AllowedIps
