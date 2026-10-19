import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryScheduler

/-! Native staging and timer callbacks retain the same historical exclusion
and physical owners in the shared journal. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

abbrev StateSafe (g : WGPrefix Journal.Event α) :=
  StatePrefixPreserves (fun h w _ => StateInv [] h w) Safe g

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved Journal.hooks pid) := by
  apply state_checked
  · intro past
    exact (show Driver.stagingObserved Quiet.nonencryptHooks pid = Driver.stagingObserved Journal.hooks pid from rfl) ▸
      Driver.staging_history Quiet.hooks_safe pid
  · intro past w a h result v b before run
    have projected := Driver.staging_projects Journal.hooks_projects pid
    rw [Driver.nonce_staging_specialization] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (native_join (EncryptionPast.send pid) (OccurrenceConfiguration.staged pid)) w a result v b before
      (DriverOwnership.state_native projected (Nonce.stagingObserved_erases pid) w v a b h run)

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved Journal.hooks pid) := by
  apply state_checked
  · intro past
    exact (show Driver.keepaliveObserved Quiet.nonencryptHooks pid = Driver.keepaliveObserved Journal.hooks pid from rfl) ▸
      Driver.keepalive_actor_history Quiet.hooks_safe.core pid
  · intro past w a h result v b before run
    have projected := Driver.keepalive_projects Journal.hooks_projects pid
    rw [Driver.nonce_keepaliveObserved_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (native_join (EncryptionPast.keepalive pid) (OccurrenceHandshake.keepalive pid)) w a result v b before
      (DriverOwnership.state_native projected (Nonce.keepaliveObserved_erases pid) w v a b h run)

theorem timer_callback (pid : PeerId) (timer : PeerTimer) : StateSafe (Driver.timerObserved Journal.hooks pid timer) := by
  apply state_checked
  · intro past
    exact (show Driver.timerObserved Quiet.nonencryptHooks pid timer = Driver.timerObserved Journal.hooks pid timer from rfl) ▸
      Driver.timer_history Quiet.hooks_safe.core pid timer
  · intro past w a h result v b before run
    have projected := Driver.timer_projects Journal.hooks_projects pid timer
    rw [Driver.nonce_timerObserved_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (native_join (EncryptionPast.timer pid timer) (OccurrenceTimers.callback pid timer)) w a result v b before
      (DriverOwnership.state_native projected (Nonce.timerObserved_erases pid timer) w v a b h run)

theorem state_product {g : WGPrefix Journal.Event α} (keeps : StateSafe g) :
    ProductSafe (liftWGObserver g) := keeps.liftWGObserver

theorem send_one : ProductSafe (liftPrefix Env.runOneSendWorker) := by
  apply product_lift
  intro past
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp
    (native_join (EncryptionPast.Maintenance.flushed_send pid) (OccurrenceDeferred.flushed_send pid))
    w.wg beforeWorker () v.wg v.ambient before worker

theorem clear_one : ProductSafe (liftPrefix Env.runOneClearWorker) := by
  apply product_lift
  intro past
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp
    (native_join (EncryptionPast.Maintenance.flushed_clear pid) (OccurrenceDeferred.flushed_clear pid))
    w.wg beforeWorker () v.wg v.ambient before worker

end Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory.Scheduler
