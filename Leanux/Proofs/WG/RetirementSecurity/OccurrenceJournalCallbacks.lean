import Leanux.Proofs.WG.RetirementSecurity.OccurrenceJournalWorkers

/-! Native staging and timer callbacks preserve the shared journal's physical
poll certificates. Their exact source terms contain no encryption poll, while
native state preservation supplies the physical boundary independently. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open OccurrenceStack TransmitSecurity

theorem checked_state_history {E α : Type} {P : WGWorld → Prop} {S : List E → Prop}
    {g : WGPrefix E α} (history : Driver.StateHistorySafe S g)
    (native : ∀ w a h result v b, P w →
      (runWGPrefix g w a h).1 = .ok ((result,v),b) → P v) :
    StatePrefixPreserves (fun h w _ => P w ∧ S h) S g := by
  intro w a h before
  obtain ⟨suffix,extension,safe,normal⟩ := history w a h before.2
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok output => exact ⟨native w a h output.1.1 output.1.2 output.2 before.1 result,safe⟩

abbrev StateSafe (g : WGPrefix Journal.Event α) :=
  StatePrefixPreserves (fun h w _ => Ready [] [] w ∧ Safe h) Safe g

theorem state_native {g : WGPrefix Journal.Event α} {native : WG.M α}
    (history : Driver.StateHistorySafe Safe g)
    (projects : StateProjectsPrefix Journal.nonce? id g (liftWGPrefix native))
    (keeps : Preserves (Ready [] []) native) : StateSafe g :=
  checked_state_history history (fun w a h result v b before run =>
    (hoare_iff_run_ambient _ _ _).mp keeps w a result v b before
      (DriverOwnership.state_native projects (erasesStatePrefix_lift _) w v a b h run))

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved Journal.hooks pid) := by
  apply checked_state_history
  · exact (show Driver.stagingObserved nonpollHooks pid = Driver.stagingObserved Journal.hooks pid from rfl) ▸
      Driver.staging_history hooks_safe pid
  · intro w a h result v b before run
    have projected := Driver.staging_projects Journal.hooks_projects pid
    rw [Driver.nonce_staging_specialization] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (OccurrenceConfiguration.staged pid) w a result v b before
      (DriverOwnership.state_native projected (Nonce.stagingObserved_erases pid) w v a b h run)

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved Journal.hooks pid) := by
  apply checked_state_history
  · exact (show Driver.keepaliveObserved nonpollHooks pid = Driver.keepaliveObserved Journal.hooks pid from rfl) ▸
      Driver.keepalive_actor_history hooks_safe.core pid
  · intro w a h result v b before run
    have projected := Driver.keepalive_projects Journal.hooks_projects pid
    rw [Driver.nonce_keepaliveObserved_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (OccurrenceHandshake.keepalive pid) w a result v b before
      (DriverOwnership.state_native projected (Nonce.keepaliveObserved_erases pid) w v a b h run)

theorem timer_callback (pid : PeerId) (timer : PeerTimer) : StateSafe (Driver.timerObserved Journal.hooks pid timer) := by
  apply checked_state_history
  · exact (show Driver.timerObserved nonpollHooks pid timer = Driver.timerObserved Journal.hooks pid timer from rfl) ▸
      Driver.timer_history hooks_safe.core pid timer
  · intro w a h result v b before run
    have projected := Driver.timer_projects Journal.hooks_projects pid timer
    rw [Driver.nonce_timerObserved_eq] at projected
    exact (hoare_iff_run_ambient _ _ _).mp (OccurrenceTimers.callback pid timer) w a result v b before
      (DriverOwnership.state_native projected (Nonce.timerObserved_erases pid timer) w v a b h run)

theorem state_product {g : WGPrefix Journal.Event α} (keeps : StateSafe g) :
    ProductSafe (liftWGObserver g) := keeps.liftWGObserver

theorem send_one : ProductSafe (liftPrefix Env.runOneSendWorker) :=
  product_lift _ OccurrenceDeferred.send_one

theorem clear_one : ProductSafe (liftPrefix Env.runOneClearWorker) :=
  product_lift _ OccurrenceDeferred.clear_one

end Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
