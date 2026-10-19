import Leanux.Proofs.WG.Queues.CurrentSlotTransmit
import Leanux.Proofs.WG.Queues.HolderAuxiliary

/-! The original scheduler is instantiated on the complete funded account,
physical ring, owner journal and all three nullable slots. The only unfinished
worker obligation is the actual receive observer on this same stronger domain. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderAuxScheduler
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open HolderAuxiliary

private theorem join (action : RxHistory.Obs α)
    (account : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) action)
    (owner : OwnerChecks.Preserves action)
    (slots : PrefixPreserves (fun _ w => CurrentSlots.Inv w.wg) (fun _ => True) action) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe action := by
  apply pair action account owner
  intro w h hi x v run
  have post := (slots w h hi.2.2).choose_spec.2.2
  simpa only [run] using post

private theorem slot_stored (g : PrefixM LifetimeEvent α) (original : Leanux.M α)
    (erase : ErasesPrefix g original) (frame : SameProductStore original) :
    PrefixPreserves (fun _ w => CurrentSlots.Inv w.wg) (fun _ => True) (RxHistory.mixed g) :=
  CurrentSlots.observed _ _ (Appends.focus _ _ _) (RxHistory.mixed_erases erase)
    (CurrentSlots.product_store_preserves frame)

/-- These are the ten actual scheduler atoms, including its copied trial.
No universal contract over arbitrary observers is assumed. -/
theorem atoms (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    RxHistory.SchedulerSource.AtomContracts (Inv initial loans before) OwnerChecks.Safe (fun {_} g => g) := by
  have account := HolderScheduler.atoms initial loans before
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    have frame : SameProductStore (monadLift a : Leanux.M α) :=
      fun _ => productAmbient_spec a _ (fun _ _ hi => hi)
    exact join _ (account.ambient a)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.mixed_lift) _ frame)
      (slot_stored _ _ (erasesPrefix_lift _) frame)
  · intro α e
    exact join _ (account.stopped e)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.mixed_throw) e)
      (slot_stored _ _ (erasesPrefix_throw e) (fun _ => hoare_throw e))
  · intro pid
    apply join _ (account.peer pid)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.peer) pid)
    apply slot_stored _ _ (liftWGObserver_erases (getPeerMixed_erases pid))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (getPeer_normal pid w v p a b run).1
  · intro id
    apply join _ (account.packet id)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.packet) id)
    apply slot_stored _ _ (liftWGObserver_erases (getTxSkbPrefix_erases id))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (Packets.getTxSkb_current id w v p a b run).1
  · intro f
    apply join _ (account.work f)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.work) f)
    apply CurrentSlots.observed _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _)))
    apply PublicationPoll.native_product CurrentSlots.Inv
    apply CurrentSlots.fields_preserves (project := id)
    intro initial
    change Preserves (fun w => CurrentSlots.fields w = initial) _
    slot_fields_step initial
  · intro a
    exact join _ (account.occupancy a)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.occupancy) a)
      (slot_stored _ _ (activationOccupancyPrefix_erases a) (activationOccupancy_sameKernel a))
  · exact join _ account.refills
      (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.refills)
      (slot_stored _ _ activationRefillsPrefix_erases activationRefills_sameKernel)
  · intro next
    exact join _ (account.pending next)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.pending) next)
      (slot_stored _ _ (pendingNapiPrefix_erases next) (SourceScheduler.pendingNapi_kernel next))
  · intro a
    exact join _ (account.hasWork a)
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.hasWork) a)
      (slot_stored _ _ (activationHasWorkPrefix_erases a) (activationHasWork_sameKernel a))
  · apply join _ account.trial OwnerChecks.filter_probe
    have frame : SameProductStore (do
        let w ← getAmbient
        w.suspended.filterM Env.Activation.consistent) :=
      (show SameProductStore getAmbient from fun _ =>
        productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)).bind
        (fun w => filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)
    exact CurrentSlots.observed _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases consistentFilterAudit_erases) (CurrentSlots.product_store_preserves frame)

theorem encrypt_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.encryptIteration :=
  join _ (HolderScheduler.encrypt_preserves initial loans before) OwnerEncrypt.encryptIteration
    CurrentSlots.encryptIteration_observed

theorem decrypt_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.decryptIteration :=
  join _ (HolderScheduler.decrypt_preserves initial loans before) OwnerCryptWorkers.decryptIteration
    CurrentSlots.decryptIteration_observed

theorem tx_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  join _ (HolderScheduler.tx_preserves initial loans before pid) (OwnerTransmit.txIteration pid)
    (CurrentSlots.TxSource.tx_observed pid)

theorem softirq_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.napiSoftirq :=
  join _ (HolderScheduler.softirq_preserves initial loans before) OwnerWorkers.napiSoftirq
    CurrentSlots.softirq_observed

theorem ahead_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves (fun _ _ hi => hi.2.1.safe) _
    (atoms initial loans before) _ (encrypt_preserves initial loans before) pid

/-- The receive-worker obligation names the original observer, not a substitute
callback or an initialized result. -/
theorem iteration_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe Origins.HistoryAdapters.receiveIteration)
    (a : Activation) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.activationIteration a) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ (atoms initial loans before) _ _ _ _ _
    (encrypt_preserves initial loans before) (ahead_preserves initial loans before)
    (tx_preserves initial loans before) (decrypt_preserves initial loans before) receive a

theorem run_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe Origins.HistoryAdapters.receiveIteration)
    (a : Activation) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.activationRun a) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves (I := Inv initial loans before) (fun _ _ hi => hi.2.1.safe)
    (fun _ _ _ same hi => store hi same) _ (atoms initial loans before) _
    (iteration_preserves initial loans before receive) a

theorem dispatch_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe Origins.HistoryAdapters.receiveIteration)
    (worker : Worker) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves (I := Inv initial loans before) (fun _ _ hi => hi.2.1.safe)
    (fun _ _ _ same hi => store hi same) _ (atoms initial loans before) _
    (run_preserves initial loans before receive) worker

theorem schedule_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe Origins.HistoryAdapters.receiveIteration)
    (stack : Option Worker) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves (I := Inv initial loans before) (fun _ _ hi => hi.2.1.safe)
    (fun _ _ _ same hi => store hi same) _ (atoms initial loans before) _ _ _
    (dispatch_preserves initial loans before receive) (run_preserves initial loans before receive)
    (softirq_preserves initial loans before) stack

theorem nested_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe Origins.HistoryAdapters.receiveIteration)
    (worker : Worker) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves (I := Inv initial loans before) (fun _ _ hi => hi.2.1.safe)
    (fun _ _ _ same hi => store hi same) _ (schedule_preserves initial loans before receive) worker

end Leanux.Proofs.WG.Queues.RxCredits.HolderAuxScheduler
