import Leanux.Proofs.WG.Noise.PendingEnvironmentFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.PendingEnvironment
open Leanux Leanux.WG Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open PendingSession PendingReception

/-- Original namespace pre-exit keeps pending allocation stamps while clearing
carrier/creator fields, sockets and endpoint sources over the actual saved peer list. -/
theorem preexit_native (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact native_socket _ (socketReinit_sameSocket _ _) seen)
    | (rx_retention_head clearPeerEndpointSrc; exact configuration_clear_endpoint _ seen)
    | (rx_retention_head get
       exact hoare_consequence (hoare_get (fun w => NativeInv w seen))
         (fun _ h => h) (fun _ _ h => h.2))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => NativeInv w seen)
       intro _ _
       change Preserves (fun w => NativeInv w seen) _)
    | pending_native_step seen

macro "pending_environment_step " seen:term : tactic => `(tactic| first
  | (rx_retention_head getWG; exact PendingScheduler.product_store _
      (fun initial => productGetWG_spec (fun s => s = initial)) $seen)
  | (rx_retention_head getRouting; exact PendingScheduler.product_store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w result v run
      cases run
      rfl) $seen)
  | (rx_retention_head modifyRouting; exact PendingScheduler.product_store _
      (fun initial => productRouting_spec _ (fun s => s = initial)) $seen)
  | (rx_retention_head modifyEnv; exact fixture_modify _ $seen)
  | (rx_retention_head Env.requireIdleDevice; exact PendingScheduler.product_store _
      PendingScheduler.requireIdleDevice_store $seen)
  | (rx_retention_head Env.inetdevDestroy; exact inetdev_destroy $seen)
  | (first
       | (rx_retention_head liftWG; apply native_product)
       | (allocation_release_lift_from WG.M; apply native_lift)
     intro prior
     first
     | (rx_retention_head WG.wgUp; exact PendingReception.up_native prior)
     | (rx_retention_head WG.wgDown; exact PendingSession.down prior)
     | (rx_retention_head WG.wgDestruct; exact (ensures_iff _ _ _).mp (PendingSession.destruct prior))
     | (rx_retention_head WG.netnsPreExit; exact preexit_native prior)
     | (rx_retention_head getDev; exact native_store _ getDev_sameWGStore prior)
     | (rx_retention_head mayHaveSlept; exact native_store _ mayHaveSlept_sameWGStore prior))
  | (allocation_release_lift_from Net.M; exact routing _ $seen)
  | (rx_retention_head skipCut; exact productAmbient_spec (AmbientM.skipCut _) _ (fun _ _ hi => hi))
  | (rx_retention_head unsupported; exact productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ hi => hi))
  | (rx_retention_head peekUnit; exact productAmbient_spec (AmbientM.peekUnit _) _ (fun _ _ hi => hi))
  | (rx_retention_head resolveUnit; exact productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ hi => hi))
  | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ hi => hi))
  | rx_retention_step)

/-- Actual environment up, including absence/already-up/socket-error branches,
below-cut inputs and the real routing notifiers. -/
theorem up (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) Env.wgUp := by
  unfold Env.wgUp
  repeat' pending_environment_step seen

theorem down (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) Env.wgDown := by
  unfold Env.wgDown
  repeat' pending_environment_step seen

/-- The exact polymorphic deletion factor retains the real notifier callbacks,
idle guard and stepped-dump rejection; no readiness premise is added. -/
theorem delete (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) Env.wgDelete := by
  rw [Configuration.envDelete_factor]
  unfold Configuration.envDeleteWith
  repeat' pending_environment_step seen

/-- Original namespace cleanup, including its foreign-creator and queued-work
checks, selected worker section and routing callbacks. -/
theorem cleanup (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) Env.netnsCleanup := by
  unfold Env.netnsCleanup Env.pendingDevice
  repeat' first
    | (rx_retention_head Env.runWorker; apply worker _ _ seen)
    | (rx_retention_head invariant; exact productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi))
    | (rx_retention_head getAmbient; exact productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi))
    | pending_environment_step seen

theorem preexit_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver netnsPreExitPrefix)) :=
  lifecycle_observed _ _ netnsPreExitPrefix_erases preexit_native

theorem up_observed : PrefixPreserves StateInv HistorySafe (RxHistory.audit envWgUpAudit) :=
  audit_observed _ _ envWgUpAudit_erases up

theorem down_observed : PrefixPreserves StateInv HistorySafe (RxHistory.audit envWgDownAudit) :=
  audit_observed _ _ envWgDownAudit_erases down

theorem delete_observed : PrefixPreserves StateInv HistorySafe (RxHistory.audit envWgDeleteAudit) :=
  audit_observed _ _ envWgDeleteAudit_erases delete

theorem cleanup_observed : PrefixPreserves StateInv HistorySafe (RxHistory.audit envNetnsCleanupAudit) :=
  audit_observed _ _ envNetnsCleanupAudit_erases cleanup

end Leanux.Proofs.WG.Noise.PendingEnvironment
