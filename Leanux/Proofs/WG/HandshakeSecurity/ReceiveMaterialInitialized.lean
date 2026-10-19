import Leanux.Proofs.WG.HandshakeSecurity.DriverDeliveryNeutral
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialConfiguration
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialOuterFrames
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! RX allocation-certificate transport through the actual shared
runner. All native callbacks and the initial empty RX store remain explicit. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity Configuration Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false
private theorem product_ite (p : Prop) [Decidable p] {a b : PrefixM Journal.Event α}
    (ha : p → PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe a) (hb : ¬p → PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe b) :
    PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe (if p then a else b) := PrefixPreserves.ite p ha hb

theorem product_fs (action : FS.M α) :
    ProductSafe (liftPrefix (liftFS action)) :=
  product_carrier_lift _ (OuterNative.fs action)

theorem product_seccomp (action : Seccomp.M α) :
    ProductSafe (liftPrefix (liftSeccomp action)) :=
  product_carrier_lift _ (OuterNative.seccomp action)

theorem product_task (action : TaskM α) :
    ProductSafe (liftPrefix (liftTask action)) :=
  product_carrier_lift _ (OuterNative.task action)

theorem product_routing (action : Net.M α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_store _ (fun initial => productRouting_spec action (· = initial))

theorem product_read : ProductSafe (liftPrefix (get : Leanux.M World)) :=
  product_carrier_lift _ OuterNative.outer_get

theorem product_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    ProductSafe (liftPrefix (_root_.modify f)) :=
  product_carrier_lift _ (OuterNative.outer_edit f same)

theorem product_editEnv (f : EnvWorld → EnvWorld) :
    ProductSafe (liftPrefix (modifyEnv f)) :=
  product_modify _ (fun _ => rfl)

theorem product_readFiles : ProductSafe (liftPrefix (getFiles : Leanux.M FilesStruct)) := by
  apply product_carrier_lift
  intro h
  have task (a : TaskM Task) : Framing.Preserves (fun w : World => Carrier h w.wg)
      (monadLift a : Leanux.M Task) := OuterNative.fs (monadLift a : FS.M Task) h
  routing_tx_source [getFiles,getTask] using [task]

theorem product_readTask (t : TaskRef) : ProductSafe (liftPrefix (getTask t : Leanux.M Task)) :=
  product_fs (monadLift (TaskM.getTask t) : FS.M Task)

theorem product_modifyFiles (f : FilesStruct → FilesStruct) :
    ProductSafe (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  product_fs (monadLift (TaskM.modifyTask .task (fun t => {t with files := f t.files})) : FS.M Unit)

macro "receive_outer_step" : tactic => `(tactic| first
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
  | receive_deferred_step)

theorem envUp :
    ProductSafe (envUpObserved Journal.hooks) := by
  change PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe _
  unfold envUpObserved
  repeat' first
    | (scheduler_preserve_at upObserved; exact product_state up)
    | receive_outer_step

theorem socketCall (fd : Nat) (body : PrefixM Journal.Event Int) (hb : ProductSafe body) :
    ProductSafe (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  change PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe _
  unfold socketCallOnWith
  apply product_bind (product_fs (fdget fd))
  intro f
  apply product_ite
  · intro _; exact product_pure _
  · intro _
    exact product_bind hb (fun ret => product_bind (product_fs (fdput f)) (fun _ => product_pure ret))

theorem netlink (body : PrefixM Journal.Event Int) (hb : ProductSafe body) :
    ProductSafe (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe _
  unfold netlinkRequestWith
  apply product_bind (socketCall _ _ (product_bind (product_ambient (AmbientM.skipCut allocCuts))
    (fun _ => product_bind hb (fun ret => product_bind (product_ambient (AmbientM.skipCut allocCuts))
      (fun _ => product_pure ret)))))
  intro ret
  exact product_bind (socketCall _ _ (product_pure 0)) (fun _ => product_pure ret)

theorem rtnetlink (body : PrefixM Journal.Event Int) (hb : ProductSafe body) :
    ProductSafe (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe _
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (scheduler_preserve_at socketCallOnWith; apply socketCall
       change PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe _)
    | receive_outer_step

theorem retained (call : Syscall)
    (kept : DispatchRetained call) : ProductSafe (retainedObserved Journal.hooks call) := by
  change PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe _
  by_cases up : call = .wgUp
  · subst call
    exact socketCall _ _ (envUp)
  · by_cases down : call = .wgDown
    · subst call
      unfold retainedObserved
      rw [envDown_lift Journal.hooks rfl rfl,socketCall_lift]
      exact product_carrier_lift _ (fun history => OuterNative.quiet_dispatch .wgDown history kept up)
    · simp only [retainedObserved]
      exact product_carrier_lift _ (fun history => OuterNative.quiet_dispatch call history kept up)

theorem observe :
    ProductSafe (observeObserved Journal.hooks) := by
  rw [DriverDelivery.observe _ rfl]
  exact product_bind (idle_timers) (fun _ => product_store _ observeTail_sameKernel)

theorem dispatchObserve :
    ProductSafe (dispatchObserveObserved Journal.hooks) := by
  change PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe _
  unfold dispatchObserveObserved
  apply product_bind (observe)
  rintro ⟨ret,json⟩
  exact product_bind (product_ambient _) (fun _ => socketCall _ _ (product_pure ret))

theorem dispatch
    (call : Syscall) : ProductSafe (dispatchObserved Journal.hooks call) := by
  apply dispatchWith_preserves
  · exact retained
  · intro attrs; exact netlink _ (product_state (configDevice_safe  attrs))
  · apply rtnetlink
    simpa only [liftWGObserver_lift] using product_state (state_native _ (fun _ => LifecycleFrames.device_create))
  · unfold dispatchDeleteObserved
    rw [envDelete_lift Journal.hooks rfl rfl rfl]
    exact rtnetlink _ (product_carrier_lift _ Control.env_delete)
  · exact syscall_xmit
  · intro family port message tos ll dest
    exact socketCall _ _ (inject family port message tos ll dest)
  · exact flood
  · exact batch
  · exact dispatchObserve

theorem syscall
    (call : Syscall) : ProductSafe (syscallObserved Journal.hooks call) :=
  SyscallSource.preserves (I := (fun h (w : World) => Carrier h w.wg)) (S := Safe)
    (fun _ _ hi => hi.2) product_wg_store call _ _ _ _ _ _ _
    (dispatch call) (send_workers) (idle_timers)
    (product_store _ routeIntoWg0_sameKernel) (after_xmit) (after_advance)
    (product_carrier_lift _ Control.env_cleanup)

/-- Every confirmation in the initialized shared journal carries the same key
allocation as the native earlier AEAD, including receipts before a later Stop. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith (fun h (w : World) => Carrier h w.wg) Safe (fun _ _ hi => hi.2)
    product_wg_store (syscallObserved Journal.hooks) syscall trace placeholders
  intro w same
  exact product_wg_store [] {w with wg:=Runner.initialWG trace.net trace.bare} w same
    (initial trace.net trace.bare)

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
