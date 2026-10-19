import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionTraffic

/-! The actual initialized Runner certifies every selected timer/work receipt
in the final journal, including prefixes retained before indexed Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem product_fs (action : FS.M α) : ProductSafe (liftPrefix (liftFS action)) :=
  product_native _ (Delayed.product_fs action)

theorem product_ambient (action : AmbientM α) : ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_native _ (Delayed.product_ambient action)

theorem product_store_lift (action : Leanux.M α) (frame : SameProductStore action) :
    ProductSafe (liftPrefix action) := product_native _ (Delayed.product_store_lift action frame)

private theorem idle_native : ProductSafe (liftPrefix Env.requireIdleDevice) :=
  product_store_lift _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store)

private theorem destroy_native : ProductSafe (liftPrefix Env.inetdevDestroy) :=
  product_store_lift _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store)

private theorem sleep_native : ProductSafe (liftPrefix (liftWG mayHaveSlept)) :=
  product_native _ (Delayed.product_wg _ (Delayed.native_store _ mayHaveSlept_sameWGStore))

open Lean Meta Elab Tactic in
elab "selection_outer_native " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a product carrier"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftPrefix do throwError "not a native lift"
  let native := action.getAppArgs.back!.consumeMData.headBeta
  let native := if native.isAppOf ``liftWG then native.getAppArgs.back! else native
  let .const actual _ := native.getAppFn | throwError "not a constant native action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different native head"

macro "selection_outer_step" : tactic => `(tactic| first
  | (selection_outer_native Env.requireIdleDevice
     exact idle_native)
  | (selection_outer_native Env.inetdevDestroy
     exact destroy_native)
  | (selection_outer_native mayHaveSlept
     exact sleep_native)
  | (selection_carrier_head liftPrefix; apply product_native; solve | causal_delayed_outer_step)
  | selection_carrier_step)

theorem envUp :
    ProductSafe (envUpObserved hooks) := by
  unfold envUpObserved
  repeat' first
    | (selection_carrier_head upObserved; exact product_state up)
    | selection_outer_step

theorem envDown :
    ProductSafe (envDownObserved hooks) := by
  unfold envDownObserved envDownWith
  repeat' first
    | (selection_carrier_head downObserved; exact product_state down)
    | selection_outer_step

theorem envDelete :
    ProductSafe (envDeleteObserved hooks) := by
  unfold envDeleteObserved HandshakeSecurity.SendExchange.envDeleteWith Configuration.envDeleteWith
  repeat' first
    | (selection_carrier_head downObserved; exact product_state down)
    | (selection_carrier_head destructObserved; exact product_state destruct)
    | selection_outer_step

theorem socketCall (fd : Nat) (body : PrefixM Event Int) (hb : ProductSafe body) :
    ProductSafe (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply product_bind (product_fs (fdget fd))
  intro f
  apply product_ite
  · intro _; exact product_pure _
  · intro _
    exact product_bind hb (fun ret => product_bind (product_fs (fdput f)) (fun _ => product_pure ret))

theorem netlink (body : PrefixM Event Int) (hb : ProductSafe body) :
    ProductSafe (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply product_bind (socketCall _ _ (product_bind (product_ambient (AmbientM.skipCut allocCuts))
    (fun _ => product_bind hb (fun ret => product_bind (product_ambient (AmbientM.skipCut allocCuts))
      (fun _ => product_pure ret)))))
  intro ret
  exact product_bind (socketCall _ _ (product_pure 0)) (fun _ => product_pure ret)

theorem rtnetlink (body : PrefixM Event Int) (hb : ProductSafe body) :
    ProductSafe (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (selection_carrier_head socketCallOnWith; apply socketCall)
    | selection_outer_step

theorem retained
    (call : Syscall)
    (kept : DispatchRetained call) : ProductSafe (retainedObserved hooks call) := by
  by_cases up : call = .wgUp
  · subst call
    exact socketCall _ _ envUp
  · by_cases stopped : call = .wgDown
    · subst call
      exact socketCall _ _ envDown
    · have same : retainedObserved hooks call = liftPrefix (Leanux.dispatch call) := by
        cases call <;> simp_all only [retainedObserved] <;> contradiction
      rw [same]
      exact product_native _ (Delayed.product_native _ (fun history => Delayed.OuterNative.quiet_dispatch call history kept up stopped))

theorem observe :
    ProductSafe (observeObserved hooks) :=
  product_bind idleTimers (fun _ => product_store_lift _ observeTail_sameKernel)

theorem dispatchObserve :
    ProductSafe (dispatchObserveObserved hooks) := by
  unfold dispatchObserveObserved
  apply product_bind observe
  rintro ⟨ret,json⟩
  exact product_bind (product_ambient _) (fun _ => socketCall _ _ (product_pure ret))

theorem dispatch
    (call : Syscall) : ProductSafe (dispatchObserved hooks call) := by
  apply dispatchWith_preserves
  · exact retained
  · intro attrs; exact netlink _ (product_state (configDevice_safe attrs))
  · apply rtnetlink
    simpa only [liftWGObserver_lift] using product_state device_create
  · exact rtnetlink _ (envDelete)
  · exact syscallXmit
  · intro family port message tos ll dest
    exact socketCall _ _ (inject family port message tos ll dest)
  · exact flood
  · exact batch
  · exact dispatchObserve

theorem syscall
    (call : Syscall) : ProductSafe (syscallObserved hooks call) :=
  SyscallSource.preserves (I := fun h w => Inv h w.wg)
    (S := Safe)
    (fun _ _ hi => hi.2) product_wg_store call _ _ _ _ _ _ _
    (dispatch call) (sendWorkers) idleTimers
    (product_store_lift _ routeIntoWg0_sameKernel) (afterXmit) (afterAdvance)
    (product_native _ (Delayed.product_native _ Delayed.env_cleanup))

theorem initial (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Inv [] w :=
  ⟨Delayed.initial net bare w same,Safe.empty⟩

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (execute trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith (fun h w => Inv h w.wg) Safe
    (fun _ _ hi => hi.2) product_wg_store (syscallObserved hooks) syscall trace placeholders
    (fun w same => initial trace.net trace.bare w.wg same)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
