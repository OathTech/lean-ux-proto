import Leanux.Proofs.WG.TransmitSecurity.BatchJournalTraffic
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastOuterFrames

/-! Configuration, native lifecycle and the complete outer Runner establish
global head/packet key agreement from empty history and initialized state. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchJournal.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open RetirementSecurity Lifetimes Queues Configuration Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem configDevice_safe (attrs : DeviceAttrs) : StateSafe (Driver.configDevice Journal.hooks attrs) := by
  apply state_checked
  · intro past
    exact (show Driver.configDevice Quiet.nonencryptHooks attrs = Driver.configDevice Journal.hooks attrs from rfl) ▸
      Driver.configDevice_history Quiet.hooks_safe.actors attrs
  · intro w a h result v b before run
    have projected := Driver.configDevice_projects Journal.hooks_projects attrs
    rw [Driver.nonce_configDevice_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (BatchCoherence.Configuration.set_device attrs) w a result v b before
      (DriverOwnership.state_native projected (Nonce.configDevice_erases attrs) w v a b h run)

theorem up : StateSafe (Driver.upObserved Journal.hooks) := by
  apply state_checked
  · intro past
    exact (show Driver.upObserved Quiet.nonencryptHooks = Driver.upObserved Journal.hooks from rfl) ▸
      Driver.up_history Quiet.hooks_safe.actors
  · intro w a h result v b before run
    have projected := Driver.up_projects Journal.hooks_projects
    rw [Driver.nonce_upObserved_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp BatchCoherence.Lifecycle.up w a result v b before
      (DriverOwnership.state_native projected Nonce.upObserved_erases w v a b h run)

private theorem product_bind {g : PrefixM Journal.Event α} {f : α → PrefixM Journal.Event β}
    (hg : PrefixPreserves (Inv []) Safe g) (hf : ∀x, PrefixPreserves (Inv []) Safe (f x)) :
    PrefixPreserves (Inv []) Safe (g >>= f) := PrefixPreserves.bind hg hf

private theorem product_ite (p : Prop) [Decidable p] {a b : PrefixM Journal.Event α}
    (ha : p → PrefixPreserves (Inv []) Safe a) (hb : ¬p → PrefixPreserves (Inv []) Safe b) :
    PrefixPreserves (Inv []) Safe (if p then a else b) := PrefixPreserves.ite p ha hb

theorem product_fs (action : FS.M α) :
    ProductSafe (liftPrefix (liftFS action)) :=
  product_lift _ (productFS_spec action _ (fun _ _ _ _ hi => hi))

theorem product_seccomp (action : Seccomp.M α) :
    ProductSafe (liftPrefix (liftSeccomp action)) :=
  product_lift _ (productSeccomp_spec action _ (fun _ _ _ _ hi => hi))

theorem product_task (action : TaskM α) :
    ProductSafe (liftPrefix (liftTask action)) :=
  product_lift _ (productTask_spec action _ (fun _ _ _ hi => hi))

theorem product_routing (action : Net.M α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_store _ (fun initial => productRouting_spec action (· = initial))

theorem product_read : ProductSafe (liftPrefix (get : Leanux.M World)) :=
  product_lift _ (hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))

theorem product_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    ProductSafe (liftPrefix (_root_.modify f)) :=
  product_lift _ (by
    apply hoare_modify
    intro w before
    exact BatchCoherence.Stack.ready_store (same w) before)

theorem product_editEnv (f : EnvWorld → EnvWorld) :
    ProductSafe (liftPrefix (modifyEnv f)) :=
  product_modify _ (fun _ => rfl)

theorem product_readFiles : ProductSafe (liftPrefix (getFiles : Leanux.M FilesStruct)) := by
  apply product_lift
  have task (a : TaskM Task) : Framing.Preserves (fun w : World => BatchCoherence.Native.Coherent [] [] w.wg)
      (monadLift a : Leanux.M Task) := productFS_spec (monadLift a : FS.M Task) _ (fun _ _ _ _ hi => hi)
  routing_tx_source [getFiles,getTask] using [task]

theorem product_readTask (t : TaskRef) : ProductSafe (liftPrefix (getTask t : Leanux.M Task)) :=
  product_fs (monadLift (TaskM.getTask t) : FS.M Task)

theorem product_modifyFiles (f : FilesStruct → FilesStruct) :
    ProductSafe (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  product_fs (monadLift (TaskM.modifyTask .task (fun t => {t with files := f t.files})) : FS.M Unit)

macro "batch_journal_outer_step" : tactic => `(tactic| first
  | origin_carrier_join_let
  | origin_carrier_join_use
  | (scheduler_preserve_at liftSeccomp; exact product_seccomp _)
  | (scheduler_preserve_at liftFS; exact product_fs _)
  | (scheduler_preserve_at liftTask; exact product_task _)
  | (scheduler_preserve_at get; exact product_read)
  | (scheduler_preserve_at getFiles; exact product_readFiles)
  | (scheduler_preserve_at getTask; exact product_readTask _)
  | (scheduler_preserve_at modifyFiles; exact product_modifyFiles _)
  | (scheduler_preserve_at modify; apply product_modify; intro w; rfl)
  | (scheduler_preserve_at skipCut; exact product_ambient _)
  | (scheduler_preserve_at modifyEnv; exact product_editEnv _)
  | (scheduler_preserve_at liftPrefix; first
     | exact product_seccomp _
     | exact product_fs _
     | exact product_task _
     | exact product_routing _)
  | origin_carrier_reduce
  | batch_journal_deferred_step)

theorem envUp :
    ProductSafe (envUpObserved Journal.hooks) := by
  change PrefixPreserves (Inv []) Safe _
  unfold envUpObserved
  repeat' first
    | (scheduler_preserve_at upObserved; exact state_product up)
    | batch_journal_outer_step

theorem socketCall (fd : Nat) (body : PrefixM Journal.Event Int) (hb : ProductSafe body) :
    ProductSafe (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  change PrefixPreserves (Inv []) Safe _
  unfold socketCallOnWith
  apply product_bind (product_fs (fdget fd))
  intro f
  apply product_ite
  · intro _; exact product_pure _
  · intro _
    exact product_bind hb (fun ret => product_bind (product_fs (fdput f)) (fun _ => product_pure ret))

theorem netlink (body : PrefixM Journal.Event Int) (hb : ProductSafe body) :
    ProductSafe (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves (Inv []) Safe _
  unfold netlinkRequestWith
  apply product_bind (socketCall _ _ (product_bind (product_ambient (AmbientM.skipCut allocCuts))
    (fun _ => product_bind hb (fun ret => product_bind (product_ambient (AmbientM.skipCut allocCuts))
      (fun _ => product_pure ret)))))
  intro ret
  exact product_bind (socketCall _ _ (product_pure 0)) (fun _ => product_pure ret)

theorem rtnetlink (body : PrefixM Journal.Event Int) (hb : ProductSafe body) :
    ProductSafe (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves (Inv []) Safe _
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (scheduler_preserve_at socketCallOnWith; apply socketCall
       change PrefixPreserves (Inv []) Safe _)
    | batch_journal_outer_step

theorem retained (call : Syscall)
    (_kept : DispatchRetained call) : ProductSafe (retainedObserved Journal.hooks call) := by
  change PrefixPreserves (Inv []) Safe _
  by_cases up : call = .wgUp
  · subst call
    exact socketCall _ _ envUp
  · by_cases down : call = .wgDown
    · subst call
      unfold retainedObserved
      rw [envDown_lift Journal.hooks rfl rfl rfl,socketCall_lift]
      exact product_lift _ (BatchCoherence.Syscalls.dispatch_native .wgDown)
    · simp only [retainedObserved,Driver.dumpDispatch_lift Journal.hooks rfl]
      exact product_lift _ (BatchCoherence.Syscalls.dispatch_native call)

theorem observe :
    ProductSafe (observeObserved Journal.hooks) := by
  change PrefixPreserves _ _ (Driver.idleTimersObserved Journal.hooks >>= fun _ =>
    AuthenticatedEffects.DeliverySource.observeWith (liftPrefix Env.deliverSent))
  rw [AuthenticatedEffects.DeliverySource.observe_native]
  exact product_bind (idle_timers) (fun _ => product_store _ observeTail_sameKernel)

theorem dispatchObserve :
    ProductSafe (dispatchObserveObserved Journal.hooks) := by
  change PrefixPreserves (Inv []) Safe _
  unfold dispatchObserveObserved
  apply product_bind (observe)
  rintro ⟨ret,json⟩
  exact product_bind (product_ambient _) (fun _ => socketCall _ _ (product_pure ret))

theorem dispatch
    (call : Syscall) : ProductSafe (dispatchObserved Journal.hooks call) := by
  apply dispatchWith_preserves
  · exact retained
  · intro attrs; exact netlink _ (state_product (configDevice_safe  attrs))
  · apply rtnetlink
    exact product_native _ BatchCoherence.Lifecycle.create
  · apply rtnetlink
    rw [Driver.envDelete_lift Journal.hooks rfl rfl rfl]
    exact product_lift _ BatchCoherence.Controls.env_delete
  · exact syscall_xmit
  · intro family port message tos ll dest
    exact socketCall _ _ (inject family port message tos ll dest)
  · exact flood
  · exact batch
  · exact dispatchObserve

theorem syscall
    (call : Syscall) : ProductSafe (syscallObserved Journal.hooks call) :=
  SyscallSource.preserves (I := (Inv [])) (S := Safe)
    (fun _ _ hi => hi.2) product_wg_store call _ _ _ _ _ _ _
    (dispatch call) (send_workers) (idle_timers)
    (product_store _ routeIntoWg0_sameKernel) (after_xmit) (after_advance)
    (product_lift _ BatchCoherence.Controls.env_cleanup)

/-- Every actual encryption receipt has matching head/packet peer and key fields
in the initialized shared driver, including receipts before a later Stop. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith (Inv []) Safe (fun _ _ hi => hi.2)
    product_wg_store (syscallObserved Journal.hooks) syscall trace placeholders
  intro w same
  have before := BatchJournal.initial trace.net trace.bare
  exact ⟨BatchCoherence.Stack.ready_store same before.1,before.2⟩

end Leanux.Proofs.WG.TransmitSecurity.BatchJournal.Scheduler
