import Leanux.Proofs.WG.AllowedIps.RoutingEnvTrafficFrames
import Leanux.Proofs.WG.Configuration.LifecycleCompletion
import Leanux.Proofs.WG.Lifetimes.EnvControlsAudit

/-! Environment controls retain routing at normal endpoints. Device deletion
uses the actual lifecycle completion observer, so its completed clear/removal
cuts survive later Stops without asserting a failed World. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false


elab "control_endpoint_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  let action ←
    if ty.isAppOf ``Hoare && args.size ≥ 3 then pure args[args.size - 3]!
    else if ty.isAppOf ``Preserves && args.size ≥ 1 then pure args.back!
    else Lean.throwError "not an endpoint contract"
  let rec head (fuel : Nat) (e : Lean.Expr) : Lean.Name :=
    match fuel with
    | 0 => .anonymous
    | n+1 =>
      let e := e.consumeMData
      match e.getAppFn with
      | .const actual _ =>
        if actual == ``liftM || actual == ``MonadLift.monadLift ||
            actual == ``MonadLiftT.monadLift then
          if e.getAppArgs.isEmpty then .anonymous else head n e.getAppArgs.back!
        else actual
      | _ => .anonymous
  let actual := head 4 action
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different endpoint action"

theorem envScalar_routing (a : Leanux.M α) (ha : SameEnvScalar a) :
    SameView (fun w : World => routingView w.wg) a :=
  ha.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => by
      simp only [routingView, envScalarView, envScalarStore, productStoreView,
        wgStoreView, envScalarDevice, Option.map_map, Function.comp_def]
      rfl)

theorem requireIdleDevice_routing :
    SameView (fun w : World => routingView w.wg) Env.requireIdleDevice := by
  intro s
  have hn := requireNoCryptWork_routing.wp (fun t => t = s)
  have hd := productGetDev_spec (fun k => k.2.2.2.dev.map routingState = s)
  have ha {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => routingView w.wg = s) (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Env.requireIdleDevice
  apply preserves_bind hn
  intro _
  apply preserves_bind hd
  intro d
  split
  · exact ha _
  · exact preserves_pure _

theorem envWgUp_routing : ProductRetainsRoutingCall Env.wgUp := by
  intro s
  have hp : Preserves (fun w : World => RetainsRouting s (routingView w.wg)) Env.wgUp := by
    have hu := RetainsRoutingCall.wp wgUp_routing.liftWG s
    have hg := productGetWG_spec (fun k => RetainsRouting s (k.2.2.2.dev.map routingState))
    have hr {α : Type} (a : Net.M α) :=
      productRouting_spec a (fun k => RetainsRouting s (k.2.2.2.dev.map routingState))
    have ha {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => RetainsRouting s (routingView w.wg))
          (MonadLift.monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    unfold Env.wgUp
    repeat' first
      | (control_endpoint_head getWG; exact hg)
      | (control_endpoint_head WG.wgUp; exact hu)
      | (control_endpoint_head skipCut; exact ha _)
      | (control_endpoint_head Net.Fib.rtCacheFlush; exact hr _)
      | (control_endpoint_head Net.Fib.netdevUp; exact hr _)
      | (control_endpoint_head modifyEnv; exact (hoare_iff_run _ _ _).mpr (fun _ _ _ hi he => by cases he; exact hi))
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (maintenance_intro; try dsimp only)
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

theorem envWgDown_routing : ProductRetainsRoutingCall Env.wgDown := by
  intro s
  have hp : Preserves (fun w : World => RetainsRouting s (routingView w.wg)) Env.wgDown := by
    have hi := requireIdleDevice_routing.wp (RetainsRouting s)
    have hd := RetainsRoutingCall.wp wgDown_routing.liftWG s
    have hg := productGetWG_spec (fun k => RetainsRouting s (k.2.2.2.dev.map routingState))
    have hr {α : Type} (a : Net.M α) :=
      productRouting_spec a (fun k => RetainsRouting s (k.2.2.2.dev.map routingState))
    have ha {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => RetainsRouting s (routingView w.wg))
          (MonadLift.monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    unfold Env.wgDown
    repeat' first
      | (control_endpoint_head getWG; exact hg)
      | (control_endpoint_head Env.requireIdleDevice; exact hi)
      | (control_endpoint_head WG.wgDown; exact hd)
      | (control_endpoint_head skipCut; exact ha _)
      | (control_endpoint_head Net.Fib.rtCacheFlush; exact hr _)
      | (control_endpoint_head Net.Fib.netdevDown; exact hr _)
      | (control_endpoint_head modifyRouting; exact hr _)
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (maintenance_intro; try dsimp only)
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

theorem envSetMtu_routing (mtu : Nat) :
    SameView (fun w : World => routingView w.wg) (Env.setMtu mtu) :=
  envScalar_routing _ (setMtu_sameEnvScalar mtu)

theorem routeIntoWg0_routing : SameView (fun w : World => routingView w.wg) Env.routeIntoWg0 :=
  routeIntoWg0_sameKernel.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)

theorem wgDeladdr_routing (family : Nat) :
    SameView (fun w : World => routingView w.wg) (Env.wgDeladdr family) :=
  (wgDeladdr_sameKernel family).of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)

theorem wgDelroute_routing (family : Nat) :
    SameView (fun w : World => routingView w.wg) (Env.wgDelroute family false 0 0 0 0 0) :=
  (wgDelroute_sameKernel family).of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)

theorem observe_routing : ProductRetainsRoutingCall Env.observe := by
  intro s
  rw [Environment.observe_eq]
  have hp : Preserves (fun w : World => RetainsRouting s (routingView w.wg))
      (do Env.idleTimers; Environment.observeTail) :=
    preserves_bind (RetainsRoutingCall.wp idleTimers_routing s) (fun _ =>
      (observeTail_sameKernel.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl)).wp (RetainsRouting s))
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

theorem netnsCleanup_routing : ProductRetainsRoutingCall Env.netnsCleanup := by
  have hb : ProductRetainsRoutingCall (do
      WG.netnsPreExit
      Net.Fib.inCreatorNs do
        Net.Fib.rtCacheFlush
        Net.Fib.netdevDown LO_IFINDEX
        Net.Fib.inetaddrDown LO_IFINDEX LOOPBACK4 8 true true
        Net.Fib.netdevUnregister LO_IFINDEX
      skipCut ([.dstCacheResetTs] ++ allocCuts)) := by
    intro s
    let tail : Net.M Unit := Net.Fib.inCreatorNs do
      Net.Fib.rtCacheFlush
      Net.Fib.netdevDown LO_IFINDEX
      Net.Fib.inetaddrDown LO_IFINDEX LOOPBACK4 8 true true
      Net.Fib.netdevUnregister LO_IFINDEX
    have hn : Preserves (fun w : World => RetainsRouting s (routingView w.wg))
        (liftWG WG.netnsPreExit) :=
      RetainsRoutingCall.wp
        (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same (project := id) netnsPreExit_routing)) s
    have ht : Preserves (fun w : World => RetainsRouting s (routingView w.wg))
        (liftWG (liftRouting tail)) :=
      productRouting_spec tail (fun k => RetainsRouting s (k.2.2.2.dev.map routingState))
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => RetainsRouting s (routingView w.wg))
          (MonadLift.monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have hc := ambient (AmbientM.skipCut ([.dstCacheResetTs] ++ allocCuts))
    have hp := preserves_bind hn (fun _ => preserves_bind ht (fun _ => hc))
    exact hoare_consequence (P' := fun w : World => routingView w.wg = s)
      (Q' := fun _ w => RetainsRouting s (routingView w.wg)) hp
      (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

  intro s
  have hp : Preserves (fun w : World => RetainsRouting s (routingView w.wg)) Env.netnsCleanup := by
    have hw := RetainsRoutingCall.wp (runWorker_routing .netnsCleanup _ hb) s
    have hr {α : Type} (a : Net.M α) :=
      productRouting_spec a (fun k => RetainsRouting s (k.2.2.2.dev.map routingState))
    have ha {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => RetainsRouting s (routingView w.wg))
          (MonadLift.monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    unfold Env.netnsCleanup
    repeat' first
      | (control_endpoint_head getRouting; exact hr _)
      | (control_endpoint_head unsupported; exact ha _)
      | (control_endpoint_head modifyEnv; exact (hoare_iff_run _ _ _).mpr (fun _ _ _ hi he => by cases he; exact hi))
      | (control_endpoint_head peekUnit; exact ha _)
      | (control_endpoint_head resolveUnit; exact ha _)
      | (control_endpoint_head Env.runWorker; exact hw)
      | (control_endpoint_head Pure.pure; exact preserves_pure _)
      | (control_endpoint_head Bind.bind; apply preserves_bind)
      | (maintenance_intro; try dsimp only)
      | (split; all_goals try contradiction)
  exact hoare_consequence hp (fun _ he => he ▸ RetainsRouting.refl _) (fun _ _ h => h)

def envWgDeleteObserved : PrefixM RoutingCompletion Int := do
  if (← liftPrefix getWG).dev.isSome then liftPrefix Env.requireIdleDevice
  let pending (sock : WG.NlSock) : Bool :=
    sock.cbRunning || sock.queue.any fun chunk => chunk.messages.any fun m => match m with | .done .. => true | _ => false
  let k ← liftPrefix getWG
  if pending k.nlSock7 || pending k.nlSock8 then
    liftPrefix (unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)")
  let onDown : PrefixM RoutingCompletion Unit := do
    liftPrefix Net.Fib.rtCacheFlush
    liftPrefix (Net.Fib.netdevDown WG0_IFINDEX)
    liftPrefix (modifyRouting fun w => { w with defaultRoute6 := false, addrs6 := [], ipv6Gen := w.ipv6Gen + 1 })
  let onUnregister : PrefixM RoutingCompletion Unit := do
    liftPrefix Env.inetdevDestroy
    liftPrefix (Net.Fib.netdevUnregister WG0_IFINDEX)
    liftPrefix (modifyRouting fun w => { w with addrs6 := [], defaultRoute6 := false, ipv6Gen := w.ipv6Gen + 1 })
  if (← liftPrefix getWG).dev.isNone then return -ENODEV
  if (← liftPrefix (liftWG getDev)).running then
    liftPrefix (liftWG WG.wgDown)
    onDown
  liftPrefix (skipCut allocCuts)
  onUnregister
  liftPrefix (liftWG mayHaveSlept)
  liftWGObserver Configuration.wgDestructObserved
  return 0

theorem envWgDeleteObserved_erases : ErasesPrefix envWgDeleteObserved Env.wgDelete := by
  unfold envWgDeleteObserved Env.wgDelete WG.wgDelete
  repeat' first
    | (maintenance_head Configuration.wgDestructObserved; exact liftWGObserver_erases Configuration.wgDestructObserved_erases)
    | control_audit_erases

theorem envWgDeleteObserved_global (initial : FlatTable × FlatTable) :
    PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg)
      (CompletionSafe initial) envWgDeleteObserved := by
  have safe : ∀ h (w : World), GlobalCompletionState initial h w.wg → CompletionSafe initial h :=
    fun _ _ hi => hi.1
  have hg : SameView (fun w : World => routingView w.wg) (getWG : Leanux.M WGWorld) :=
    fun s => productGetWG_spec (fun k => k.2.2.2.dev.map routingState = s)
  have hr {α : Type} (a : Net.M α) :
      SameView (fun w : World => routingView w.wg)
        (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α) :=
    fun s => productRouting_spec a (fun k => k.2.2.2.dev.map routingState = s)
  have ha {α : Type} (a : AmbientM α) :
      SameView (fun w : World => routingView w.wg) (MonadLift.monadLift a : Leanux.M α) :=
    fun s => productAmbient_spec a _ (fun _ _ h => h)
  have hd := sameView_liftWG (fun w : World => routingView w.wg) routingView
    getDev (routing_kernel (project := id) _ getDev_sameWGStore) (fun _ _ _ h => h)
  have hm := sameView_liftWG (fun w : World => routingView w.wg) routingView
    mayHaveSlept (routing_kernel (project := id) _ mayHaveSlept_sameWGStore) (fun _ _ _ h => h)
  have hi : SameView (fun w : World => routingView w.wg) Env.inetdevDestroy := by
    unfold Env.inetdevDestroy
    apply SameView.bind (hr (getRouting : Net.M Net.Routing))
    intro routing
    apply SameView.bind (hr (modifyRouting fun s => {s with addrs4 := [], addrPlens4 := []}))
    intro _
    apply SameView.bind
    · apply DumpComposition.forIn_sameView
      intro a rest
      apply SameView.bind (hr (Net.Fib.inetaddrDown WG0_IFINDEX a
        ((routing.addrPlens4.lookup a).getD 32) (rest.drop 1).isEmpty true))
      intro _
      exact SameView.pure _ _
    intro _
    exact SameView.pure _ _
  apply PrefixEnsures.preserves
  unfold envWgDeleteObserved
  repeat' first
    | contradiction
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head Configuration.wgDestructObserved; exact (Configuration.wgDestructObserved_global initial).liftWGObserver)
    | (audit_contract_head Env.inetdevDestroy; exact global_completion_same World.wg initial _ hi)
    | (audit_contract_head getWG; exact global_completion_same World.wg initial _ hg)
    | (audit_contract_head Env.requireIdleDevice; exact global_completion_same World.wg initial _ requireIdleDevice_routing)
    | (audit_contract_head liftWG; first
        | exact global_completion_lift World.wg initial _ wgDown_routing.liftWG
        | exact global_completion_same World.wg initial _ hd
        | exact global_completion_same World.wg initial _ hm)
    | (control_audit_routing; exact global_completion_same World.wg initial _ (hr _))
    | (audit_contract_head liftPrefix; exact global_completion_same World.wg initial _ (ha _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h (w : World) => GlobalCompletionState initial h w.wg))
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.forInInvariant _ _ _ (fun _ h (w : World) => GlobalCompletionState initial h w.wg) _ safe)
    | maintenance_intro
    | (with_reducible split)

end Leanux.Proofs.WG.AllowedIps
