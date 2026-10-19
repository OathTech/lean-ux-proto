import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginDriverConfiguration
import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginOuterFrames
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! TX ciphertext-origin transport through the actual shared
runner. All native callbacks and the initial empty TX store remain explicit. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false
private theorem product_bind {g : PrefixM Journal.Event α} {f : α → PrefixM Journal.Event β}
    (hg : PrefixPreserves ProductInv Safe g) (hf : ∀x, PrefixPreserves ProductInv Safe (f x)) :
    PrefixPreserves ProductInv Safe (g >>= f) := PrefixPreserves.bind hg hf

private theorem product_ite (p : Prop) [Decidable p] {a b : PrefixM Journal.Event α}
    (ha : p → PrefixPreserves ProductInv Safe a) (hb : ¬p → PrefixPreserves ProductInv Safe b) :
    PrefixPreserves ProductInv Safe (if p then a else b) := PrefixPreserves.ite p ha hb

theorem product_fs (action : FS.M α) :
    ProductSafe (liftPrefix (liftFS action)) :=
  product_lift _ (OuterNative.fs action)

theorem product_seccomp (action : Seccomp.M α) :
    ProductSafe (liftPrefix (liftSeccomp action)) :=
  product_lift _ (OuterNative.seccomp action)

theorem product_task (action : TaskM α) :
    ProductSafe (liftPrefix (liftTask action)) :=
  product_lift _ (OuterNative.task action)

theorem product_routing (action : Net.M α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_store _ (fun initial => productRouting_spec action (· = initial))

theorem product_read : ProductSafe (liftPrefix (get : Leanux.M World)) :=
  product_lift _ OuterNative.outer_get

theorem product_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    ProductSafe (liftPrefix (_root_.modify f)) :=
  product_lift _ (OuterNative.outer_edit f same)

theorem product_editEnv (f : EnvWorld → EnvWorld) :
    ProductSafe (liftPrefix (modifyEnv f)) :=
  product_modify _ (fun _ => rfl)

theorem product_readFiles : ProductSafe (liftPrefix (getFiles : Leanux.M FilesStruct)) := by
  apply product_lift
  intro h
  have task (a : TaskM Task) : Framing.Preserves (fun w : World => Inv h w.wg)
      (monadLift a : Leanux.M Task) := OuterNative.fs (monadLift a : FS.M Task) h
  routing_tx_source [getFiles,getTask] using [task]

theorem product_readTask (t : TaskRef) : ProductSafe (liftPrefix (getTask t : Leanux.M Task)) :=
  product_fs (monadLift (TaskM.getTask t) : FS.M Task)

theorem product_modifyFiles (f : FilesStruct → FilesStruct) :
    ProductSafe (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  product_fs (monadLift (TaskM.modifyTask .task (fun t => {t with files := f t.files})) : FS.M Unit)

macro "ciphertext_outer_step" : tactic => `(tactic| first
  | ciphertext_carrier_join_let
  | ciphertext_carrier_join_use
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
  | ciphertext_carrier_reduce
  | ciphertext_driver_deferred_step)

theorem envUp :
    ProductSafe (envUpObserved Journal.hooks) := by
  change PrefixPreserves ProductInv Safe _
  unfold envUpObserved
  repeat' first
    | (scheduler_preserve_at upObserved; exact product_state up)
    | ciphertext_outer_step

theorem socketCall (fd : Nat) (body : PrefixM Journal.Event Int) (hb : ProductSafe body) :
    ProductSafe (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  change PrefixPreserves ProductInv Safe _
  unfold socketCallOnWith
  apply product_bind (product_fs (fdget fd))
  intro f
  apply product_ite
  · intro _; exact product_pure _
  · intro _
    exact product_bind hb (fun ret => product_bind (product_fs (fdput f)) (fun _ => product_pure ret))

theorem netlink (body : PrefixM Journal.Event Int) (hb : ProductSafe body) :
    ProductSafe (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves ProductInv Safe _
  unfold netlinkRequestWith
  apply product_bind (socketCall _ _ (product_bind (product_ambient (AmbientM.skipCut allocCuts))
    (fun _ => product_bind hb (fun ret => product_bind (product_ambient (AmbientM.skipCut allocCuts))
      (fun _ => product_pure ret)))))
  intro ret
  exact product_bind (socketCall _ _ (product_pure 0)) (fun _ => product_pure ret)

theorem rtnetlink (body : PrefixM Journal.Event Int) (hb : ProductSafe body) :
    ProductSafe (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves ProductInv Safe _
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (scheduler_preserve_at socketCallOnWith; apply socketCall
       change PrefixPreserves ProductInv Safe _)
    | ciphertext_outer_step

theorem retained (call : Syscall)
    (kept : DispatchRetained call) : ProductSafe (retainedObserved Journal.hooks call) := by
  change PrefixPreserves ProductInv Safe _
  by_cases up : call = .wgUp
  · subst call
    exact socketCall _ _ (envUp)
  · by_cases down : call = .wgDown
    · subst call
      unfold retainedObserved
      rw [envDown_lift Journal.hooks rfl,socketCall_lift]
      exact product_lift _ (fun history => OuterNative.quiet_dispatch .wgDown history kept up)
    · simp only [retainedObserved]
      exact product_lift _ (fun history => OuterNative.quiet_dispatch call history kept up)

theorem observe :
    ProductSafe (observeObserved Journal.hooks) := by
  change PrefixPreserves _ _ (Driver.idleTimersObserved Journal.hooks >>= fun _ =>
    AuthenticatedEffects.DeliverySource.observeWith (liftPrefix Env.deliverSent))
  rw [AuthenticatedEffects.DeliverySource.observe_native]
  exact product_bind (idle_timers) (fun _ => product_store _ observeTail_sameKernel)

theorem dispatchObserve :
    ProductSafe (dispatchObserveObserved Journal.hooks) := by
  change PrefixPreserves ProductInv Safe _
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
    simpa only [liftWGObserver_lift] using product_state (state_lift _ (fun _ => NativeFrames.device_create))
  · unfold dispatchDeleteObserved
    rw [envDelete_lift Journal.hooks rfl]
    exact rtnetlink _ (product_lift _ Control.env_delete)
  · exact syscall_xmit
  · intro family port message tos ll dest
    exact socketCall _ _ (inject family port message tos ll dest)
  · exact flood
  · exact batch
  · exact dispatchObserve

theorem syscall
    (call : Syscall) : ProductSafe (syscallObserved Journal.hooks call) :=
  SyscallSource.preserves (I := ProductInv) (S := Safe)
    (fun _ _ hi => hi.2) product_wg_store call _ _ _ _ _ _ _
    (dispatch call) (send_workers) (idle_timers)
    (product_store _ routeIntoWg0_sameKernel) (after_xmit) (after_advance)
    (product_lift _ Control.env_cleanup)

/-- Every nonempty socket payload in the initialized shared journal has
strictly earlier native encryption evidence, including stopped prefixes. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith ProductInv Safe (fun _ _ hi => hi.2)
    product_wg_store (syscallObserved Journal.hooks) syscall trace placeholders
  intro w same
  refine ⟨product_wg_store_inv [] {w with wg:=Runner.initialWG trace.net trace.bare} w same
    (initial trace.net trace.bare),?_⟩
  intro pre event post position
  cases pre <;> cases position

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
