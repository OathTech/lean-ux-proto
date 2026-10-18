import Leanux.Proofs.WG.Queues.BaseCoherenceHistory
import Leanux.Proofs.WG.Queues.SchedulerPreservation

/-! The original scheduler retains structural fields through its concrete
workers, accesses and copied trials. No whole-observer preservation premise
replaces an actual callback. Only normal outcomes have a final state. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem mixed_structure (initial) (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erase : ErasesPrefix g a) (same : SameProductStore a) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.mixed g) :=
  observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.mixed_erases erase) (product_store_view same)

theorem scheduler_atoms (initial) : RxHistory.SchedulerSource.AtomContracts
    (fun _ w => view w.wg=initial) (fun _ => True) (fun {_} g => g) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact mixed_structure initial _ _ (erasesPrefix_lift _)
      (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))
  · intro α e
    exact mixed_structure initial _ _ (erasesPrefix_throw e) (fun _ => hoare_throw e)
  · intro pid
    apply mixed_structure initial _ _ (liftWGObserver_erases (getPeerMixed_erases pid))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (getPeer_normal pid w v p a b run).1
  · intro id
    apply mixed_structure initial _ _ (liftWGObserver_erases (getTxSkbPrefix_erases id))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (Packets.getTxSkb_current id w v p a b run).1
  · intro f
    apply observed_structure initial _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _)))
    apply native_product_view
    intro s
    change Preserves (fun w => view w=s) _
    base_rx_step s
  · intro a
    exact mixed_structure initial _ _ (activationOccupancyPrefix_erases a) (activationOccupancy_sameKernel a)
  · intro next
    exact mixed_structure initial _ _ (pendingNapiPrefix_erases next) (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact mixed_structure initial _ _ (activationHasWorkPrefix_erases a) (activationHasWork_sameKernel a)
  · have same : SameProductStore (do let w ← getAmbient; w.suspended.filterM Env.Activation.consistent) :=
      (show SameProductStore getAmbient from fun _ => productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)).bind
        (fun w => filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)
    exact observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases consistentFilterAudit_erases)
      (product_store_view same)

theorem cryptAhead_structure (initial) (pid : PeerId) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves (fun _ _ _ => True.intro) _
    (scheduler_atoms initial) _ (encryptIteration_structure initial) pid

theorem activationIteration_structure (initial) (a : Activation) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.activationIteration a) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ (scheduler_atoms initial) _ _ _ _ _
    (encryptIteration_structure initial) (cryptAhead_structure initial)
    (txIteration_structure initial) (decryptIteration_structure initial) (receiveIteration_structure initial) a

theorem activationRun_structure (initial) (a : Activation) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.activationRun a) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves (I := fun _ w => view w.wg=initial) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => (product_view_transport same).trans hi) _ (scheduler_atoms initial) _
    (activationIteration_structure initial) a

theorem dispatch_structure (initial) (worker : Worker) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves (I := fun _ w => view w.wg=initial) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => (product_view_transport same).trans hi) _ (scheduler_atoms initial) _
    (activationRun_structure initial) worker

theorem schedule_structure (initial) (stack : Option Worker) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves (I := fun _ w => view w.wg=initial) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => (product_view_transport same).trans hi) _ (scheduler_atoms initial) _ _ _
    (dispatch_structure initial) (activationRun_structure initial) (softirq_structure initial) stack

theorem nestedResched_structure (initial) (worker : Worker) :
    PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves (I := fun _ w => view w.wg=initial) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => (product_view_transport same).trans hi) _ (schedule_structure initial) worker

/-- Exact structural preservation lifts any supplied coherent entry to its
same actual endpoint; it does not derive coherence from configured identity. -/
theorem coherence_of_structure {E α : Type} {g : PrefixM E α}
    (frame : ∀ initial, PrefixPreserves (fun _ w => view w.wg=initial) (fun _ => True) g) :
    PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,hist,safe,post⟩ := frame (view w.wg) w h rfl
  refine ⟨suffix,hist,safe,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at post
    exact transport hi post

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
