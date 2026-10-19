import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierLifecycle
import Leanux.Proofs.WG.AuthenticatedEffects.TransportOuterNative
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! State-dependent RX authentication transport through the actual shared
runner. All native callbacks and the initial empty receive store remain explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

theorem product_native (action : Leanux.M α)
    (frame : ∀ h, Framing.Preserves (fun w : World => TransportPublication.Inv h w.wg) action) :
    ProductSafe extra origin replay (liftPrefix action) :=
  (PrefixEnsures.lift (P := ProductInv extra origin replay)
    (S := fun h => TransportReplay.Safe origin replay h ∧ extra h)
    (Q := fun _ => ProductInv extra origin replay) action (fun _ _ hi => hi.2)
    (fun h w x v hi run => ⟨(hoare_iff_run _ _ _).mp (frame (h.filterMap origin)) w x v hi.1 run,hi.2⟩)).preserves

theorem product_fs (action : FS.M α) :
    ProductSafe extra origin replay (liftPrefix (liftFS action)) :=
  product_native _ (TransportOuterNative.fs action)

theorem product_seccomp (action : Seccomp.M α) :
    ProductSafe extra origin replay (liftPrefix (liftSeccomp action)) :=
  product_native _ (TransportOuterNative.seccomp action)

theorem product_task (action : TaskM α) :
    ProductSafe extra origin replay (liftPrefix (liftTask action)) :=
  product_native _ (TransportOuterNative.task action)

theorem product_routing (action : Net.M α) :
    ProductSafe extra origin replay (liftPrefix (monadLift action : Leanux.M α)) :=
  product_storeLift _ (fun initial => productRouting_spec action (· = initial))

theorem product_read : ProductSafe extra origin replay (liftPrefix (get : Leanux.M World)) :=
  product_native _ TransportOuterNative.outer_get

theorem product_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    ProductSafe extra origin replay (liftPrefix (modify f)) :=
  product_native _ (TransportOuterNative.outer_edit f same)

theorem product_editEnv (f : EnvWorld → EnvWorld) :
    ProductSafe extra origin replay (liftPrefix (modifyEnv f)) :=
  product_modify _ (fun _ => rfl)

theorem product_readFiles : ProductSafe extra origin replay (liftPrefix (getFiles : Leanux.M FilesStruct)) := by
  apply product_native
  intro h
  have task (a : TaskM Task) : Framing.Preserves (fun w : World => TransportPublication.Inv h w.wg)
      (monadLift a : Leanux.M Task) := TransportOuterNative.fs (monadLift a : FS.M Task) h
  routing_tx_source [getFiles,getTask] using [task]

theorem product_readTask (t : TaskRef) : ProductSafe extra origin replay (liftPrefix (getTask t : Leanux.M Task)) :=
  product_fs (monadLift (TaskM.getTask t) : FS.M Task)

theorem product_modifyFiles (f : FilesStruct → FilesStruct) :
    ProductSafe extra origin replay (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  product_fs (monadLift (TaskM.modifyTask .task (fun t => {t with files := f t.files})) : FS.M Unit)

macro "transport_outer_step" : tactic => `(tactic| first
  | (transport_product_native liftSeccomp; exact product_seccomp _)
  | (transport_product_native liftFS; exact product_fs _)
  | (transport_product_native liftTask; exact product_task _)
  | (transport_product_native get; exact product_read)
  | (transport_product_native getFiles; exact product_readFiles)
  | (transport_product_native getTask; exact product_readTask _)
  | (transport_product_native modifyFiles; exact product_modifyFiles _)
  | (transport_product_native modify; apply product_modify; intro w; rfl)
  | (transport_product_native skipCut; exact product_ambient _)
  | (transport_product_native modifyEnv; exact product_editEnv _)
  | solve | transport_deferred_native
  | (transport_carrier_head liftPrefix; first
     | exact product_seccomp _
     | exact product_fs _
     | exact product_task _
     | exact product_routing _)
  | transport_deferred_step)

theorem envUp (h : StagingSafe extra origin replay hooks) :
    ProductSafe extra origin replay (envUpObserved hooks) := by
  unfold envUpObserved
  repeat' first
    | (transport_carrier_head upObserved; exact product_state (up h))
    | transport_outer_step

theorem envDown (flushed : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid)) :
    ProductSafe extra origin replay (envDownObserved hooks) := by
  unfold envDownObserved envDownWith
  repeat' first
    | (transport_carrier_head downObserved; exact product_state (down flushed))
    | (transport_product_native Env.requireIdleDevice
       exact product_storeLift _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store))
    | transport_outer_step

theorem envDelete (flushed : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid)) :
    ProductSafe extra origin replay (envDeleteObserved hooks) := by
  unfold envDeleteObserved HandshakeSecurity.SendExchange.envDeleteWith Configuration.envDeleteWith
  repeat' first
    | (transport_carrier_head downObserved; exact product_state (down flushed))
    | (transport_carrier_head destructObserved; exact product_state (destruct flushed))
    | (transport_product_native Env.requireIdleDevice
       exact product_storeLift _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store))
    | (transport_product_native liftWG
       apply product_wg
       exact TransportPublication.store_rx _ mayHaveSlept_sameWGStore)
    | (transport_product_native Env.inetdevDestroy
       exact product_storeLift _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store))
    | transport_outer_step

theorem socketCall (fd : Nat) (body : PrefixM E Int) (hb : ProductSafe extra origin replay body) :
    ProductSafe extra origin replay (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply product_bind (product_fs (fdget fd))
  intro f
  apply product_ite
  · intro _; exact product_pure _
  · intro _
    exact product_bind hb (fun ret => product_bind (product_fs (fdput f)) (fun _ => product_pure ret))

theorem netlink (body : PrefixM E Int) (hb : ProductSafe extra origin replay body) :
    ProductSafe extra origin replay (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply product_bind (socketCall _ _ (product_bind (product_ambient (AmbientM.skipCut allocCuts))
    (fun _ => product_bind hb (fun ret => product_bind (product_ambient (AmbientM.skipCut allocCuts))
      (fun _ => product_pure ret)))))
  intro ret
  exact product_bind (socketCall _ _ (product_pure 0)) (fun _ => product_pure ret)

theorem rtnetlink (body : PrefixM E Int) (hb : ProductSafe extra origin replay body) :
    ProductSafe extra origin replay (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (transport_carrier_head socketCallOnWith; apply socketCall)
    | transport_outer_step

theorem retained (h : StagingSafe extra origin replay hooks)
    (flushed : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid)) (call : Syscall)
    (kept : DispatchRetained call) : ProductSafe extra origin replay (retainedObserved hooks call) := by
  by_cases up : call = .wgUp
  · subst call
    exact socketCall _ _ (envUp h)
  · by_cases stopped : call = .wgDown
    · subst call
      exact socketCall _ _ (envDown flushed)
    · have same : retainedObserved hooks call = liftPrefix (Leanux.dispatch call) := by
        cases call <;> simp_all only [retainedObserved] <;> contradiction
      rw [same]
      exact product_native _ (fun history => TransportOuterNative.quiet_dispatch call history kept up)

theorem observe (h : DeferredSafe extra origin replay hooks) :
    ProductSafe extra origin replay (observeObserved hooks) :=
  product_bind (idleTimers h) (fun _ => product_storeLift _ observeTail_sameKernel)

theorem dispatchObserve (h : DeferredSafe extra origin replay hooks) :
    ProductSafe extra origin replay (dispatchObserveObserved hooks) := by
  unfold dispatchObserveObserved
  apply product_bind (observe h)
  rintro ⟨ret,json⟩
  exact product_bind (product_ambient _) (fun _ => socketCall _ _ (product_pure ret))

theorem dispatch (h : DeferredSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (call : Syscall) : ProductSafe extra origin replay (dispatchObserved hooks call) := by
  apply dispatchWith_preserves
  · exact retained h.toStagingSafe h.flushedSend
  · intro attrs; exact netlink _ (product_state (configDevice_safe h.toStagingSafe h.flushedSend attrs))
  · apply rtnetlink
    simpa only [liftWGObserver_lift] using product_state (extra := extra) (origin := origin)
      (replay := replay) (state_native _ TransportLifecycle.create)
  · exact rtnetlink _ (envDelete h.flushedSend)
  · exact syscallXmit h front
  · intro family port message tos ll dest
    exact socketCall _ _ (inject h family port message tos ll dest)
  · exact flood h
  · exact batch h front
  · exact dispatchObserve h

theorem syscall (h : DeferredSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (call : Syscall) : ProductSafe extra origin replay (syscallObserved hooks call) :=
  SyscallSource.preserves (I := ProductInv extra origin replay)
    (S := fun h => TransportReplay.Safe origin replay h ∧ extra h)
    (fun _ _ hi => hi.2) product_wg_store call _ _ _ _ _ _ _
    (dispatch h front call) (sendWorkers h) (idleTimers h)
    (product_storeLift _ routeIntoWg0_sameKernel) (afterXmit h) (afterAdvance h)
    (product_native _ TransportControl.env_cleanup)

/-- The initialized shared-driver run transports both positional replay
certificates and the supplied extra history property through the same execution.
All hook obligations remain explicit until the concrete Journal instantiation. -/
theorem initialized (h : DeferredSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (empty : extra []) (trace : Runner.Trace) (placeholders : Bool) :
    TransportReplay.Safe origin replay (runPrefixOuter (executeObserved hooks trace placeholders) []).2 ∧
      extra (runPrefixOuter (executeObserved hooks trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith (ProductInv extra origin replay)
    (fun h => TransportReplay.Safe origin replay h ∧ extra h)
    (fun _ _ hi => hi.2) product_wg_store (syscallObserved hooks) (syscall h front) trace placeholders
  intro w same
  refine ⟨TransportPublication.initial trace.net trace.bare w.wg same,?_,empty⟩
  intro pre event post position
  cases pre <;> cases position

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
