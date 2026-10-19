import Leanux.Proofs.WG.TransmitSecurity.StagedEnvironment
import Leanux.Proofs.WG.TransmitSecurity.StagedOuterFrames
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Staged packet provenance through the actual initialized runner, including
receipts retained when a later operation stops. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem product_fs (action : FS.M α) :
    ProductSafe (liftPrefix (liftFS action)) :=
  product_lift _ (OuterNative.fs action)

theorem product_seccomp (action : Seccomp.M α) :
    ProductSafe (liftPrefix (liftSeccomp action)) :=
  product_lift _ (OuterNative.seccomp action)

theorem product_task (action : TaskM α) :
    ProductSafe (liftPrefix (liftTask action)) :=
  product_lift _ (OuterNative.task action)

theorem product_read : ProductSafe (liftPrefix (get : Leanux.M World)) :=
  product_lift _ OuterNative.outer_get

theorem product_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    ProductSafe (liftPrefix (_root_.modify f)) :=
  product_lift _ (OuterNative.outer_edit f same)

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

macro "staged_outer_step" : tactic => `(tactic| first
  | (staged_origin_product_native liftSeccomp; exact product_seccomp _)
  | (staged_origin_product_native liftFS; exact product_fs _)
  | (staged_origin_product_native liftTask; exact product_task _)
  | (staged_origin_product_native get; exact product_read)
  | (staged_origin_product_native getFiles; exact product_readFiles)
  | (staged_origin_product_native getTask; exact product_readTask _)
  | (staged_origin_product_native modifyFiles; exact product_modifyFiles _)
  | (staged_origin_product_native modify; apply product_modify; intro w; rfl)
  | (staged_origin_product_head liftPrefix; first | exact product_seccomp _ | exact product_fs _ | exact product_task _)
  | staged_environment_step)

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
    | (staged_origin_product_head socketCallOnWith; apply socketCall
       change ProductSafe _)
    | staged_outer_step

theorem retained (call : Syscall) (kept : DispatchRetained call) :
    ProductSafe (retainedObserved hooks call) := by
  by_cases isUp : call = .wgUp
  · subst call
    exact socketCall _ _ env_up
  · by_cases isDown : call = .wgDown
    · subst call
      exact socketCall _ _ env_down
    · have eq : retainedObserved hooks call =
          RetirementSecurity.NestedPeerRelease.dumpDispatch (nestedOps hooks) call := by
        cases call <;> first | contradiction | rfl
      rw [eq]
      have quiet := CallbackFrames.dump_dispatch_quiet selection? (fun _ => rfl) call
      exact product_quiet quiet.1 quiet.2 (CallbackFrames.dump_dispatch_erases call)
        (fun history => OuterNative.quiet_dispatch call history kept isUp isDown)

theorem observe : ProductSafe (observeObserved hooks) :=
  product_bind idleTimers (fun _ => DeliverySource.observe_preserves
    (fun _ _ before => before.2) product_stable _ delivery)

theorem dispatchObserve : ProductSafe (dispatchObserveObserved hooks) := by
  unfold dispatchObserveObserved
  apply product_bind observe
  rintro ⟨ret,json⟩
  exact product_bind (product_ambient _) (fun _ => socketCall _ _ (product_pure ret))

theorem dispatch (call : Syscall) : ProductSafe (dispatchObserved hooks call) := by
  apply dispatchWith_preserves
  · exact retained
  · intro attrs; exact netlink _ (product_state (config_device attrs))
  · apply rtnetlink
    exact product_wg _ (state_lift _ (fun _ => Native.device_create))
  · exact rtnetlink _ env_delete
  · exact syscallXmit
  · intro family port message tos ll dest
    exact socketCall _ _ (inject family port message tos ll dest)
  · exact flood
  · exact batch
  · exact dispatchObserve

theorem syscall (call : Syscall) : ProductSafe (syscallObserved hooks call) :=
  SyscallSource.preserves (I := fun h w => Carrier h w.wg) (S := Safe)
    (fun _ _ hi => hi.2) product_wg_store call _ _ _ _ _ _ _
    (dispatch call) sendWorkers idleTimers
    (product_store_lift _ routeIntoWg0_sameKernel) afterXmit afterAdvance
    (product_lift _ OuterNative.env_cleanup)

theorem initial (net bare : Bool) : Inv [] (Runner.initialWG net bare) := by
  intro generation epoch pid stamp packets resident
  cases net <;> cases bare <;> simp [stagedAt,Runner.initialWG] at resident

/-- Every staged selection in an initialized native run has ordered, distinct
prior staging origins for its peer allocation, including receipts before Stop. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith (fun h w => Carrier h w.wg) Safe (fun _ _ hi => hi.2)
    product_wg_store (syscallObserved hooks) syscall trace placeholders
  intro w same
  exact product_wg_store [] {w with wg:=Runner.initialWG trace.net trace.bare} w same
    ⟨initial trace.net trace.bare,Safe.empty⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
