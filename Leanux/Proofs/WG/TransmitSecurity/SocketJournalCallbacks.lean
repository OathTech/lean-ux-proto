import Leanux.Proofs.WG.TransmitSecurity.SocketJournalScheduler

/-! Native staging and timer callbacks retain the same receipt agreement
and native batch projection in the shared journal. -/
namespace Leanux.Proofs.WG.TransmitSecurity.SocketJournal.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

abbrev StateSafe (g : WGPrefix Journal.Event α) :=
  StatePrefixPreserves (fun h w _ => StateInv [] h w) Safe g

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved Journal.hooks pid) := by
  apply state_checked
  · intro past
    exact (show Driver.stagingObserved Quiet.nontxHooks pid = Driver.stagingObserved Journal.hooks pid from rfl) ▸
      Driver.staging_history Quiet.hooks_safe pid
  · intro w a h result v b before run
    have projected := Driver.staging_projects Journal.hooks_projects pid
    rw [Driver.nonce_staging_specialization] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (BatchCoherence.Native.send_coherent pid) w a result v b before
      (DriverOwnership.state_native projected (Nonce.stagingObserved_erases pid) w v a b h run)

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved Journal.hooks pid) := by
  apply state_checked
  · intro past
    exact (show Driver.keepaliveObserved Quiet.nontxHooks pid = Driver.keepaliveObserved Journal.hooks pid from rfl) ▸
      Driver.keepalive_actor_history Quiet.hooks_safe.core pid
  · intro w a h result v b before run
    have projected := Driver.keepalive_projects Journal.hooks_projects pid
    rw [Driver.nonce_keepaliveObserved_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (BatchCoherence.Native.keepalive pid) w a result v b before
      (DriverOwnership.state_native projected (Nonce.keepaliveObserved_erases pid) w v a b h run)

theorem timer_callback (pid : PeerId) (timer : PeerTimer) : StateSafe (Driver.timerObserved Journal.hooks pid timer) := by
  apply state_checked
  · intro past
    exact (show Driver.timerObserved Quiet.nontxHooks pid timer = Driver.timerObserved Journal.hooks pid timer from rfl) ▸
      Driver.timer_history Quiet.hooks_safe.core pid timer
  · intro w a h result v b before run
    have projected := Driver.timer_projects Journal.hooks_projects pid timer
    rw [Driver.nonce_timerObserved_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (BatchCoherence.Native.callback pid timer) w a result v b before
      (DriverOwnership.state_native projected (Nonce.timerObserved_erases pid timer) w v a b h run)

theorem state_product {g : WGPrefix Journal.Event α} (keeps : StateSafe g) :
    ProductSafe (liftWGObserver g) := keeps.liftWGObserver

theorem send_one : ProductSafe (liftPrefix Env.runOneSendWorker) :=
  product_lift _ BatchCoherence.Deferred.send_one

theorem clear_one : ProductSafe (liftPrefix Env.runOneClearWorker) :=
  product_lift _ BatchCoherence.Deferred.clear_one

end Leanux.Proofs.WG.TransmitSecurity.SocketJournal.Scheduler
