import Leanux.Proofs.WG.Queues.BaseCoherenceScheduler
import Leanux.Proofs.WG.Queues.BaseCoherenceTimers
import Leanux.Proofs.WG.Queues.DeferredPreservation

/-! Exact structural frames through actual deferred dispatch. Timer scans may
use arbitrary saved Devices because this predicate observes only the current
base list and rows; no saved-identity or owner assertion is inferred. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem sendOne_view : SameView (fun w : World => view w.wg) Env.runOneSendWorker := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  exact (ProjectedAction.iff_run_ambient _ _ _).mp (flushedSend_view pid)
    w.wg beforeWorker () v.wg v.ambient worker

private theorem clearOne_view : SameView (fun w : World => view w.wg) Env.runOneClearWorker := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  exact (ProjectedAction.iff_run_ambient _ _ _).mp (flushedClear_view pid)
    w.wg beforeWorker () v.wg v.ambient worker

private theorem deferred_ambient {initial : List PeerId × List (Key × PeerId)} (action : AmbientM α) :
    Preserves (fun w : World => view w.wg=initial) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

private theorem deferred_stored {initial : List PeerId × List (Key × PeerId)} (frame : SameProductStore action) :
    Preserves (fun w : World => view w.wg=initial) action := product_store_view frame initial

theorem timerSection_view (kind : Worker) (body : Leanux.M Unit) (keeps : SameView (fun w : World => view w.wg) body) :
    SameView (fun w : World => view w.wg) (Env.runTimerSection kind body) := by
  have worker := runWorker_sameView (fun w : World => view w.wg)
    (fun _ _ same => product_view_transport same)
    kind body keeps
  intro initial
  change Preserves (fun w : World => view w.wg = initial) _
  unfold Env.runTimerSection
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (rx_retention_head Env.runWorker; exact worker initial)
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact deferred_ambient _)
    | (allocation_release_lift_from AmbientM; exact deferred_ambient _)
    | rx_retention_step

theorem stepComplete_view (bucket : UInt64) : SameView (fun w : World => view w.wg) (Env.requireStepComplete bucket) := by
  intro initial
  change Preserves (fun w : World => view w.wg = initial) _
  unfold Env.requireStepComplete
  apply preserves_bind (deferred_stored (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases TimerWheel.anotherAtStep d bucket with
  | none => exact preserves_pure _
  | some pair => cases pair; exact hoare_throw _

macro "base_timer_product_step" : tactic => `(tactic| first
  | (rx_retention_head Env.timerWorker; exact deferred_stored (timerWorker_sameKernel _))
  | (rx_retention_head Env.requireStepComplete; exact stepComplete_view _ _)
  | (rx_retention_head getWG; exact deferred_stored (fun initial => productGetWG_spec (fun s => s = initial)))
  | (rx_retention_head modifyWG; exact deferred_stored (fun initial => productModifyWG_spec
      (fun s => s = initial) _ (fun _ => rfl)))
  | (rx_retention_head throw; exact hoare_throw _)
  | (allocation_release_lift_from AmbientM; exact deferred_ambient _)
  | rx_retention_step)

theorem timerDispatch_view (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    SameView (fun w : World => view w.wg) (timerDispatchUnit kind pid timer entry prior) := by
  intro initial
  change Preserves (fun w : World => view w.wg = initial) _
  unfold timerDispatchUnit
  simp (config := {zeta := false}) only [peekUnit]
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact timerSection_view _ _ (native_product_view _ (timerCallback_view _ _)) initial)
    | (allocation_release_lift_from WG.M; exact native_product_view _ (delTimer_view _ _) initial)
    | base_timer_product_step

theorem placeholderTimer_view (j : UInt64) : SameView (fun w : World => view w.wg) (RxHistory.placeholderTimerPassSource j) := by
  intro initial
  change Preserves (fun w : World => view w.wg = initial) _
  unfold RxHistory.placeholderTimerPassSource
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact timerSection_view _ _ (native_product_view _ (timerCallback_view _ _)) initial)
    | (allocation_release_lift_from WG.M; first
        | exact deferred_stored (liftWG_sameProductStore getDev getDev_sameWGStore)
        | exact native_product_view _ (delTimer_view _ _) initial)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => view w.wg = initial)
       intro _ _
       change Preserves (fun w : World => view w.wg = initial) _)
    | base_timer_product_step

theorem nothingDue_view (j : UInt64) : SameView (fun w : World => view w.wg) (Env.requireNothingDue j) := by
  have later (kind : Worker) (unit : Nat) : SameProductStore (Env.sectionAppearsLater kind unit) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  intro initial
  change Preserves (fun w : World => view w.wg = initial) _
  unfold Env.requireNothingDue
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.sectionAppearsLater; exact deferred_stored (later _ _))
    | base_timer_product_step


private theorem drained_view (what : String) (queues : List Bool) :
    SameView (fun w : World => view w.wg) (Env.requireDrained what queues) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  exact congrArg (fun w : World => view w.wg) (requireDrained_normal what queues w v run).1

private theorem idleDevice_view : SameView (fun w : World => view w.wg) Env.requireIdleDevice := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  exact congrArg (fun w : World => view w.wg) (idleDevice_normal w v run).1

/-- The saved timer scan is pure with respect to this view, even for a supplied
saved Device. This is not an unconditional owner or identity scan contract. -/
theorem deferred_atoms (initial) : RxHistory.DeferredSource.AtomContracts
    (fun _ w => view w.wg=initial) (fun _ => True) (fun {_} g => g) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact observed_structure initial _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases runOneSendWorkerAudit_erases) sendOne_view
  · exact observed_structure initial _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases runOneClearWorkerAudit_erases) clearOne_view
  · intro what queues
    exact observed_structure initial _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (requireDrainedPrefix_erases what queues)) (drained_view what queues)
  · exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases getDevSavedAudit_erases)
      (product_store_view (liftWG_sameProductStore getDev getDev_sameWGStore))
  · intro d j
    exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (wheelNextDueAudit_erases d j))
      (SameView.pure _ _)
  · intro bucket
    exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (requireStepCompleteAudit_erases bucket))
      (stepComplete_view bucket)
  · intro j
    exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (requireNothingDueAudit_erases j))
      (nothingDue_view j)
  · intro kind pid timer entry prior
    exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (timerDispatchAudit_erases kind pid timer entry prior))
      (timerDispatch_view kind pid timer entry prior)
  · intro j
    exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (RxHistory.placeholderTimerPass_erases j))
      (placeholderTimer_view j)
  · exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.mixed_erases requireIdleDevicePrefix_erases)
      idleDevice_view
  · exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (erasesPrefix_lift _))
      (product_store_view requireNoCryptWork_sameKernel)
  · intro timer
    exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (erasesPrefix_lift _))
      (product_store_view (timerWorker_sameKernel timer))
  · intro ticks
    exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (advanceAudit_erases ticks))
      (product_store_view (advance_sameKernel ticks))

theorem runCryptWorkers_structure (initial) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves (I := fun _ w => view w.wg=initial)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => (product_view_transport same).trans hi) _
    (schedule_structure initial none)

theorem runSendWorkers_structure (initial) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) RxHistory.runSendWorkers := by
  rw [RxHistory.DeferredSource.send_factor]
  exact RxHistory.DeferredSource.send_preserves (I := fun _ w => view w.wg=initial)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => (product_view_transport same).trans hi) _
    (deferred_atoms initial) _ (schedule_structure initial none)

theorem afterXmit_structure (initial) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) RxHistory.afterXmit := by
  rw [RxHistory.DeferredSource.afterXmit_factor]
  exact RxHistory.DeferredSource.afterXmit_preserves (I := fun _ w => view w.wg=initial)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => (product_view_transport same).trans hi) _
    (deferred_atoms initial) _ (runCryptWorkers_structure initial) _ (runSendWorkers_structure initial)

theorem runTimers_structure (initial) (j : UInt64) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.runTimers j) := by
  rw [RxHistory.DeferredSource.timers_factor]
  exact RxHistory.DeferredSource.timers_preserves (I := fun _ w => view w.wg=initial)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => (product_view_transport same).trans hi) _
    (deferred_atoms initial) _ (runCryptWorkers_structure initial) j

theorem placeholderTimers_structure (initial) (j : UInt64) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.runTimersPlaceholder j) := by
  rw [RxHistory.DeferredSource.placeholder_factor]
  exact RxHistory.DeferredSource.placeholder_preserves (I := fun _ w => view w.wg=initial)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => (product_view_transport same).trans hi) _
    (deferred_atoms initial) _ (runCryptWorkers_structure initial) _ (runSendWorkers_structure initial) j

theorem idleTimers_structure (initial) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) RxHistory.idleTimers := by
  rw [RxHistory.DeferredSource.idle_factor]
  exact RxHistory.DeferredSource.idle_preserves (I := fun _ w => view w.wg=initial)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => (product_view_transport same).trans hi) _
    (deferred_atoms initial) _ (runTimers_structure initial) _ (placeholderTimers_structure initial)

theorem afterAdvance_structure (initial) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) RxHistory.afterAdvance := by
  rw [RxHistory.DeferredSource.afterAdvance_factor]
  exact RxHistory.DeferredSource.afterAdvance_preserves (I := fun _ w => view w.wg=initial)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => (product_view_transport same).trans hi) _
    (deferred_atoms initial) _ (runTimers_structure initial) _ (placeholderTimers_structure initial)

theorem deferred_structure (initial) (call : EnvDeferredCall) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.deferred call) := by
  rw [RxHistory.DeferredSource.deferred_factor]
  exact RxHistory.DeferredSource.deferred_preserves
    (I := fun _ w => view w.wg=initial) (S := fun _ => True)
    _ (deferred_atoms initial) _ _ _ _ _ _ _
    (runCryptWorkers_structure initial) (runSendWorkers_structure initial) (afterXmit_structure initial)
    (runTimers_structure initial) (placeholderTimers_structure initial) (idleTimers_structure initial)
    (afterAdvance_structure initial) call

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
