import Leanux.Proofs.WG.Noise.PendingSchedulerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingScheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PendingSession

theorem safe (h : List RxHistory.Event) (w : World) (hi : StateInv h w) :
    HistorySafe h := hi.2.2.distinct

theorem mixed_store {α : Type} (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erase : ErasesPrefix g a) (frame : SameProductStore a) :
    PrefixPreserves StateInv HistorySafe (RxHistory.mixed g) :=
  mixed_observed g a erase (product_store a frame)

theorem audit_store {α : Type} (g : AuditM α) (a : Leanux.M α)
    (erase : ErasesPrefix g a) (frame : SameProductStore a) :
    PrefixPreserves StateInv HistorySafe (RxHistory.audit g) :=
  audit_observed g a erase (product_store a frame)

/-- Real scheduler atoms; the consistency filter executes on copied Worlds and
its focused audit cannot add committed confirmation labels. -/
theorem atoms :
    RxHistory.SchedulerSource.AtomContracts StateInv HistorySafe (fun {_} a => a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact mixed_store _ _ (erasesPrefix_lift _)
      (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))
  · intro α e
    exact mixed_store _ _ (erasesPrefix_throw e) (fun _ => hoare_throw e)
  · intro pid
    apply lifecycle_observed _ _ (getPeerMixed_erases pid)
    intro seen
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v after hi run
    exact (getPeer_normal pid w v p ambient after run).1 ▸ hi
  · intro id
    exact lifecycle_observed _ _ (getTxSkbPrefix_erases id) (keeps_packet (SkbStore.getTx id))
  · intro f
    apply lifecycle_observed _ _ (erasesStatePrefix_lift _)
    intro seen
    exact PendingReception.native_modifyDevice
      (fun d => {d with txWorkQueue := f d.txWorkQueue})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) seen
  · intro a
    exact mixed_store _ _ (activationOccupancyPrefix_erases a) (activationOccupancy_sameKernel a)
  · intro next
    exact mixed_store _ _ (pendingNapiPrefix_erases next) (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact mixed_store _ _ (activationHasWorkPrefix_erases a) (activationHasWork_sameKernel a)
  · apply audit_store _ _ consistentFilterAudit_erases
    exact (show SameProductStore getAmbient from fun initial =>
      productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)).bind
        (fun w => filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)

theorem receive_iteration : PrefixPreserves StateInv HistorySafe Origins.HistoryAdapters.receiveIteration := by
  unfold Origins.HistoryAdapters.receiveIteration
  exact workerIterPrefix_preserves _ _ safe PendingReception.receiveStep
    (viewLiftPrefix_preserves productStoreView safe state_product_store (condResched_sameKernel .receiveWorker))

/-- These are obligations about the three unchanged original worker observers,
not replacement callbacks or assumptions that an individual execution succeeds. -/
structure Workers : Prop where
  encrypt : PrefixPreserves StateInv HistorySafe RxHistory.encryptIteration
  decrypt : PrefixPreserves StateInv HistorySafe RxHistory.decryptIteration
  transmit : ∀ pid, PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker))))

theorem crypt_ahead (workers : Workers) (pid : PeerId) :
    PrefixPreserves StateInv HistorySafe (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves safe _ atoms _ workers.encrypt pid

theorem iteration (workers : Workers) (a : Activation) :
    PrefixPreserves StateInv HistorySafe (RxHistory.activationIteration a) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ atoms _ _ _ _ _
    workers.encrypt (crypt_ahead workers) workers.transmit workers.decrypt receive_iteration a

theorem activation_run (workers : Workers) (a : Activation) :
    PrefixPreserves StateInv HistorySafe (RxHistory.activationRun a) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves safe state_product_store _ atoms _
    (iteration workers) a

theorem dispatch (workers : Workers) (worker : Worker) :
    PrefixPreserves StateInv HistorySafe (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves safe state_product_store _ atoms _
    (activation_run workers) worker

theorem schedule (workers : Workers)
    (caller : Option Worker) :
    PrefixPreserves StateInv HistorySafe (RxHistory.schedule caller) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves safe state_product_store _ atoms _ _ _
    (dispatch workers) (activation_run workers) actual_napi_softirq caller

theorem nested (workers : Workers)
    (worker : Worker) :
    PrefixPreserves StateInv HistorySafe (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves safe state_product_store _ (schedule workers) worker


/-- Exact native calls still requiring their own normal transport proofs.
No replacement action is introduced. -/
structure DeferredLeaves : Prop where
  timer : ∀ worker pid timer entry prior seen,
    Preserves (fun w : World => NativeInv w.wg seen)
      (timerDispatchUnit worker pid timer entry prior)
  placeholder : ∀ j seen, Preserves (fun w : World => NativeInv w.wg seen)
    (RxHistory.placeholderTimerPassSource j)

theorem deferred_atoms (leaves : DeferredLeaves) :
    RxHistory.DeferredSource.AtomContracts StateInv HistorySafe (fun {_} a => a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact audit_observed _ _ runOneSendWorkerAudit_erases PendingSession.run_one_send
  · exact audit_observed _ _ runOneClearWorkerAudit_erases PendingSession.run_one_clear
  · intro what queues
    exact mixed_store _ _ (requireDrainedPrefix_erases what queues)
      (requireDrained_store what queues)
  · exact audit_store _ _ getDevSavedAudit_erases (liftWG_sameProductStore _ getDev_sameWGStore)
  · intro d j
    exact audit_store _ _ (wheelNextDueAudit_erases d j) (SameView.pure _ _)
  · intro bucket
    exact audit_store _ _ (requireStepCompleteAudit_erases bucket) (requireStepComplete_store bucket)
  · intro j
    exact audit_store _ _ (requireNothingDueAudit_erases j) (requireNothingDue_store j)
  · intro worker pid timer entry prior
    exact audit_observed _ _ (timerDispatchAudit_erases worker pid timer entry prior)
      (leaves.timer worker pid timer entry prior)
  · intro j
    exact audit_observed _ _ (RxHistory.placeholderTimerPass_erases j) (leaves.placeholder j)
  · exact mixed_store _ _ requireIdleDevicePrefix_erases requireIdleDevice_store
  · exact audit_store _ _ (erasesPrefix_lift _) requireNoCryptWork_sameKernel
  · intro timer
    exact audit_store _ _ (erasesPrefix_lift _) (timerWorker_sameKernel timer)
  · intro ticks
    exact audit_store _ _ (advanceAudit_erases ticks) (advance_sameKernel ticks)

theorem crypt (workers : Workers) :
    PrefixPreserves StateInv HistorySafe RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves safe state_product_store _ (schedule workers none)

theorem send (workers : Workers) (leaves : DeferredLeaves) :
    PrefixPreserves StateInv HistorySafe RxHistory.runSendWorkers := by
  rw [RxHistory.DeferredSource.send_factor]
  exact RxHistory.DeferredSource.send_preserves safe state_product_store _ (deferred_atoms leaves)
    _ (schedule workers none)

theorem afterXmit (workers : Workers) (leaves : DeferredLeaves) :
    PrefixPreserves StateInv HistorySafe RxHistory.afterXmit := by
  rw [RxHistory.DeferredSource.afterXmit_factor]
  exact RxHistory.DeferredSource.afterXmit_preserves safe state_product_store _ (deferred_atoms leaves)
    _ (crypt workers) _ (send workers leaves)

theorem timers (workers : Workers) (leaves : DeferredLeaves) (j : UInt64) :
    PrefixPreserves StateInv HistorySafe (RxHistory.runTimers j) := by
  rw [RxHistory.DeferredSource.timers_factor]
  exact RxHistory.DeferredSource.timers_preserves safe state_product_store _ (deferred_atoms leaves)
    _ (crypt workers) j

theorem placeholder (workers : Workers) (leaves : DeferredLeaves) (j : UInt64) :
    PrefixPreserves StateInv HistorySafe (RxHistory.runTimersPlaceholder j) := by
  rw [RxHistory.DeferredSource.placeholder_factor]
  exact RxHistory.DeferredSource.placeholder_preserves safe state_product_store _ (deferred_atoms leaves)
    _ (crypt workers) _ (send workers leaves) j

theorem idle (workers : Workers) (leaves : DeferredLeaves) :
    PrefixPreserves StateInv HistorySafe RxHistory.idleTimers := by
  rw [RxHistory.DeferredSource.idle_factor]
  exact RxHistory.DeferredSource.idle_preserves safe state_product_store _ (deferred_atoms leaves)
    _ (timers workers leaves) _ (placeholder workers leaves)

theorem afterAdvance (workers : Workers) (leaves : DeferredLeaves) :
    PrefixPreserves StateInv HistorySafe RxHistory.afterAdvance := by
  rw [RxHistory.DeferredSource.afterAdvance_factor]
  exact RxHistory.DeferredSource.afterAdvance_preserves safe state_product_store _ (deferred_atoms leaves)
    _ (timers workers leaves) _ (placeholder workers leaves)

theorem deferred (workers : Workers) (leaves : DeferredLeaves) (call : EnvDeferredCall) :
    PrefixPreserves StateInv HistorySafe (RxHistory.deferred call) := by
  rw [RxHistory.DeferredSource.deferred_factor]
  exact RxHistory.DeferredSource.deferred_preserves _ (deferred_atoms leaves)
    _ _ _ _ _ _ _ (crypt workers) (send workers leaves) (afterXmit workers leaves)
    (timers workers leaves) (placeholder workers leaves) (idle workers leaves)
    (afterAdvance workers leaves) call

end Leanux.Proofs.WG.Noise.PendingScheduler
