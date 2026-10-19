import Leanux.Proofs.WG.RetirementSecurity.OccurrenceJournalTraffic
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverControl
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Initialized shared-runner coverage of actual encryption poll inputs. Native
physical ownership and exact journal history follow the same source callbacks;
this is separate from initialized key-reference accounting. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity
open Lifetimes Queues Configuration Driver OccurrenceStack
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem configDevice_safe (attrs : DeviceAttrs) : StateSafe (Driver.configDevice Journal.hooks attrs) := by
  apply checked_state_history
  · exact (show Driver.configDevice nonpollHooks attrs = Driver.configDevice Journal.hooks attrs from rfl) ▸
      Driver.configDevice_history hooks_safe.actors attrs
  · intro w a h result v b before run
    have projected := Driver.configDevice_projects Journal.hooks_projects attrs
    rw [Driver.nonce_configDevice_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (OccurrenceConfiguration.set_device attrs) w a result v b before
      (DriverOwnership.state_native projected (Nonce.configDevice_erases attrs) w v a b h run)

theorem up : StateSafe (Driver.upObserved Journal.hooks) := by
  apply checked_state_history
  · exact (show Driver.upObserved nonpollHooks = Driver.upObserved Journal.hooks from rfl) ▸
      Driver.up_history hooks_safe.actors
  · intro w a h result v b before run
    have projected := Driver.up_projects Journal.hooks_projects
    rw [Driver.nonce_upObserved_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp OccurrenceLifecycle.up w a result v b before
      (DriverOwnership.state_native projected Nonce.upObserved_erases w v a b h run)

private theorem product_bind {g : PrefixM Journal.Event α} {f : α → PrefixM Journal.Event β}
    (hg : PrefixPreserves (Inv []) Safe g) (hf : ∀x, PrefixPreserves (Inv []) Safe (f x)) :
    PrefixPreserves (Inv []) Safe (g >>= f) := PrefixPreserves.bind hg hf

private theorem product_ite (p : Prop) [Decidable p] {a b : PrefixM Journal.Event α}
    (ha : p → PrefixPreserves (Inv []) Safe a) (hb : ¬p → PrefixPreserves (Inv []) Safe b) :
    PrefixPreserves (Inv []) Safe (if p then a else b) := PrefixPreserves.ite p ha hb

theorem product_fs (action : FS.M α) :
    ProductSafe (liftPrefix (liftFS action)) :=
  product_lift _ (OccurrenceDispatch.fs action)

theorem product_seccomp (action : Seccomp.M α) :
    ProductSafe (liftPrefix (liftSeccomp action)) :=
  product_lift _ (OccurrenceDispatch.seccomp action)

theorem product_task (action : TaskM α) :
    ProductSafe (liftPrefix (liftTask action)) :=
  product_lift _ (OccurrenceDispatch.task action)

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
    exact ready_store (same w) before)

theorem product_editEnv (f : EnvWorld → EnvWorld) :
    ProductSafe (liftPrefix (modifyEnv f)) :=
  product_modify _ (fun _ => rfl)

theorem product_readFiles : ProductSafe (liftPrefix (getFiles : Leanux.M FilesStruct)) := by
  apply product_lift
  have task (a : TaskM Task) : Framing.Preserves (fun w : World => Ready [] [] w.wg)
      (monadLift a : Leanux.M Task) := OccurrenceDispatch.fs (monadLift a : FS.M Task)
  routing_tx_source [getFiles,getTask] using [task]

theorem product_readTask (t : TaskRef) : ProductSafe (liftPrefix (getTask t : Leanux.M Task)) :=
  product_fs (monadLift (TaskM.getTask t) : FS.M Task)

theorem product_modifyFiles (f : FilesStruct → FilesStruct) :
    ProductSafe (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  product_fs (monadLift (TaskM.modifyTask .task (fun t => {t with files := f t.files})) : FS.M Unit)

macro "occurrence_journal_outer_step" : tactic => `(tactic| first
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
  | occurrence_journal_deferred_step)

theorem envUp :
    ProductSafe (envUpObserved Journal.hooks) := by
  change PrefixPreserves (Inv []) Safe _
  unfold envUpObserved
  repeat' first
    | (scheduler_preserve_at upObserved; exact state_product up)
    | occurrence_journal_outer_step

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
    | occurrence_journal_outer_step

theorem retained (call : Syscall)
    (kept : DispatchRetained call) : ProductSafe (retainedObserved Journal.hooks call) := by
  change PrefixPreserves (Inv []) Safe _
  by_cases up : call = .wgUp
  · subst call
    exact socketCall _ _ (envUp)
  · by_cases down : call = .wgDown
    · subst call
      apply socketCall
      rw [Driver.envDown_lift Journal.hooks rfl]
      exact product_lift _ OccurrenceControls.env_down
    · cases call <;> first
        | exact False.elim (up rfl)
        | exact False.elim (down rfl)
        | exact product_lift _ (OccurrenceSyscall.dispatch_native _)

theorem observe :
    ProductSafe (observeObserved Journal.hooks) :=
  product_bind (idle_timers) (fun _ => product_store _ observeTail_sameKernel)

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
    exact product_native _ OccurrenceLifecycle.create
  · apply rtnetlink
    rw [Driver.envDelete_lift Journal.hooks rfl]
    exact product_lift _ OccurrenceControls.env_delete
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
    (product_lift _ OccurrenceControls.env_cleanup)

/-- Every actual poll receipt in the initialized shared journal has a physically
owned input, including receipts retained by a later Stop. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith (Inv []) Safe (fun _ _ hi => hi.2)
    product_wg_store (syscallObserved Journal.hooks) syscall trace placeholders
  intro w same
  refine ⟨ready_store same (OccurrenceLifecycle.initial trace.net trace.bare),?_⟩
  intro receipt member
  cases member

end Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
