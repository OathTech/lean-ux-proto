import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedCleanup
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! The final delayed-effect state carrier crosses actual syscall boundaries.
These source contracts are the base for positional selection proofs; they do
not infer selection validity from successful final-state preservation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false
theorem product_fs (action : FS.M α) :
    ProductSafe (liftPrefix (liftFS action)) :=
  product_native _ (OuterNative.fs action)

theorem product_seccomp (action : Seccomp.M α) :
    ProductSafe (liftPrefix (liftSeccomp action)) :=
  product_native _ (OuterNative.seccomp action)

theorem product_task (action : TaskM α) :
    ProductSafe (liftPrefix (liftTask action)) :=
  product_native _ (OuterNative.task action)

theorem product_routing (action : Net.M α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_store_lift _ (fun initial => productRouting_spec action (· = initial))

theorem product_read : ProductSafe (liftPrefix (get : Leanux.M World)) :=
  product_native _ OuterNative.outer_get

theorem product_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    ProductSafe (liftPrefix (modify f)) :=
  product_native _ (OuterNative.outer_edit f same)

theorem product_editEnv (f : EnvWorld → EnvWorld) :
    ProductSafe (liftPrefix (modifyEnv f)) :=
  product_modify _ (fun _ => rfl)

theorem product_readFiles : ProductSafe (liftPrefix (getFiles : Leanux.M FilesStruct)) := by
  apply product_native
  intro h
  have task (a : TaskM Task) : Framing.Preserves (fun w : World => Inv h w.wg)
      (monadLift a : Leanux.M Task) := OuterNative.fs (monadLift a : FS.M Task) h
  routing_tx_source [getFiles,getTask] using [task]

theorem product_readTask (t : TaskRef) : ProductSafe (liftPrefix (getTask t : Leanux.M Task)) :=
  product_fs (monadLift (TaskM.getTask t) : FS.M Task)

theorem product_modifyFiles (f : FilesStruct → FilesStruct) :
    ProductSafe (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  product_fs (monadLift (TaskM.modifyTask .task (fun t => {t with files := f t.files})) : FS.M Unit)

macro "causal_delayed_outer_step" : tactic => `(tactic| first
  | (causal_delayed_product_native liftSeccomp; exact product_seccomp _)
  | (causal_delayed_product_native liftFS; exact product_fs _)
  | (causal_delayed_product_native liftTask; exact product_task _)
  | (causal_delayed_product_native get; exact product_read)
  | (causal_delayed_product_native getFiles; exact product_readFiles)
  | (causal_delayed_product_native getTask; exact product_readTask _)
  | (causal_delayed_product_native modifyFiles; exact product_modifyFiles _)
  | (causal_delayed_product_native modify; apply product_modify; intro w; rfl)
  | (causal_delayed_product_native skipCut; exact product_ambient _)
  | (causal_delayed_product_native modifyEnv; exact product_editEnv _)
  | solve | causal_delayed_deferred_native
  | (causal_delayed_head liftPrefix; first
     | exact product_seccomp _
     | exact product_fs _
     | exact product_task _
     | exact product_routing _)
  | causal_delayed_deferred_step)

theorem envUp :
    ProductSafe (envUpObserved hooks) := by
  unfold envUpObserved
  repeat' first
    | (causal_delayed_head upObserved; exact product_state up)
    | causal_delayed_outer_step

theorem envDown :
    ProductSafe (envDownObserved hooks) := by
  unfold envDownObserved envDownWith
  repeat' first
    | (causal_delayed_head downObserved; exact product_state down)
    | (causal_delayed_product_native Env.requireIdleDevice
       exact product_store_lift _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store))
    | causal_delayed_outer_step

theorem envDelete :
    ProductSafe (envDeleteObserved hooks) := by
  unfold envDeleteObserved HandshakeSecurity.SendExchange.envDeleteWith Configuration.envDeleteWith
  repeat' first
    | (causal_delayed_head downObserved; exact product_state down)
    | (causal_delayed_head destructObserved; exact product_state destruct)
    | (causal_delayed_product_native Env.requireIdleDevice
       exact product_store_lift _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store))
    | (causal_delayed_product_native liftWG
       exact product_wg _ (native_store _ mayHaveSlept_sameWGStore))
    | (causal_delayed_product_native Env.inetdevDestroy
       exact product_store_lift _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store))
    | causal_delayed_outer_step

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
    | (causal_delayed_head socketCallOnWith; apply socketCall)
    | causal_delayed_outer_step

theorem retained
    (call : Syscall)
    (kept : DispatchRetained call) : ProductSafe (retainedObserved hooks call) := by
  by_cases up : call = .wgUp
  · subst call
    exact socketCall _ _ envUp
  · by_cases stopped : call = .wgDown
    · subst call
      exact socketCall _ _ envDown
    · have same : retainedObserved hooks call =
          RetirementSecurity.NestedPeerRelease.dumpDispatch (nestedOps hooks) call := by
        cases call <;> simp_all only [retainedObserved] <;> contradiction
      rw [same]
      exact observed_product _ _ (CallbackFrames.dump_dispatch_erases call)
        (CallbackFrames.dump_dispatch_quiet (fun _ : Event => (none : Option Empty)) (fun _ => rfl) call).1
        (fun history => OuterNative.quiet_dispatch call history kept up stopped)

theorem observe :
    ProductSafe (observeObserved hooks) :=
  product_bind idleTimers (fun _ => DeliverySource.observe_preserves (fun _ _ _ => True.intro) product_store _ deliver)

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
    (S := fun _ => True)
    (fun _ _ _ => True.intro) product_wg_store call _ _ _ _ _ _ _
    (dispatch call) (sendWorkers) idleTimers
    (product_store_lift _ routeIntoWg0_sameKernel) (afterXmit) (afterAdvance)
    (product_native _ env_cleanup)

/-- The actual fixture has neither resident pending timers nor queued handshake
work, whether it starts with wg0, without networking, or as a bare trace. -/
theorem initial (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  have device : w.dev = (Runner.initialWG net bare).dev := congrArg WGStoreView.dev same
  refine ⟨?_,[],QueuedOccurrences.Carrier.empty w ?_⟩
  · intro pid timer stamp expires entry pending
    cases net <;> cases bare <;>
      simp [TimerSlots.Pending,TimerSlots.view,device,Runner.initialWG] at pending
  · cases net <;> cases bare <;>
      simp [QueuedOccurrences.queue,device,Runner.initialWG]

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
