import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerSource
import Leanux.Proofs.WG.TimerDiscipline.HookDeferredAtomsSource
import Leanux.Proofs.WG.TimerDiscipline.HookStateFrames
import Leanux.Proofs.WG.Noise.PendingSchedulerFrames
/-! Canonical administrative scheduler/deferred frames. Actual observer erasure is used before applying the existing seven-field store contracts. The mutable TX-work write is an explicit argument. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookState
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do
variable {E : Type} {I : List E → World → Prop} {S : List E → Prop}
theorem old_store (safe : ∀ h w, I h w → S h) (transport : StoreTransport I)
    {α : Type} (observed : RxHistory.Obs α) (action : Leanux.M α)
    (erases : ErasesPrefix observed action) (frame : SameProductStore action) :
    PrefixPreserves I S (HookScheduler.old observed) := by
  rw [HookScheduler.old_eq observed action erases]
  exact lift_store safe transport action frame
theorem scheduler_atoms (safe : ∀ h w, I h w → S h) (transport : StoreTransport I)
    (work : ∀ f : List PeerId → List PeerId, PrefixPreserves I S
      (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})))) :
    RxHistory.SchedulerSource.AtomContracts I S (fun {_} a => HookScheduler.old a) := by
  have stored {α : Type} (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
      (erases : ErasesPrefix g a) (frame : SameProductStore a) :
      PrefixPreserves I S (HookScheduler.old (RxHistory.mixed g)) :=
    old_store safe transport _ a (RxHistory.mixed_erases erases) frame
  constructor
  · intro α a
    exact stored _ _ (erasesPrefix_lift _)
      (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))
  · intro α e
    exact stored _ _ (erasesPrefix_throw e) (fun _ => hoare_throw e)
  · intro pid
    exact stored _ _ (liftWGObserver_erases (getPeerMixed_erases pid))
      (liftWG_sameProductStore _ (by
        apply (ProjectedAction.iff_run_ambient _ _ _).mpr
        intro g a p v b run
        exact congrArg wgStoreView (Peers.getPeer_current pid g v p a b run).1))
  · intro id
    apply stored _ _ (liftWGObserver_erases (getTxSkbPrefix_erases id))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro g a p v b run
    exact congrArg wgStoreView (Packets.getTxSkb_current id g v p a b run).1
  · intro f
    rw [HookScheduler.old_native]
    exact work f
  · intro a
    exact stored _ _ (activationOccupancyPrefix_erases a) (activationOccupancy_sameKernel a)
  · intro next
    exact stored _ _ (pendingNapiPrefix_erases next) (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact stored _ _ (activationHasWorkPrefix_erases a) (activationHasWork_sameKernel a)
  · apply old_store safe transport _ _ (RxHistory.audit_erases consistentFilterAudit_erases)
    exact (show SameProductStore getAmbient from fun initial =>
      productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)).bind
        (fun w => filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)
theorem deferred_atoms (safe : ∀ h w, I h w → S h) (transport : StoreTransport I) :
    Noise.DriverTags.Deferred.QuietAtoms I S (fun {_} a => HookScheduler.old a) := by
  constructor
  · intro what queues
    exact old_store safe transport _ _ (RxHistory.mixed_erases (requireDrainedPrefix_erases what queues))
      (Noise.PendingScheduler.requireDrained_store what queues)
  · exact old_store safe transport _ _ (RxHistory.audit_erases getDevSavedAudit_erases)
      (liftWG_sameProductStore _ getDev_sameWGStore)
  · intro d j
    exact old_store safe transport _ _ (RxHistory.audit_erases (wheelNextDueAudit_erases d j))
      (fun _ => preserves_pure _)
  · intro b
    exact old_store safe transport _ _ (RxHistory.audit_erases (requireStepCompleteAudit_erases b))
      (Noise.PendingScheduler.requireStepComplete_store b)
  · intro j
    exact old_store safe transport _ _ (RxHistory.audit_erases (requireNothingDueAudit_erases j))
      (Noise.PendingScheduler.requireNothingDue_store j)
  · exact old_store safe transport _ _ (RxHistory.mixed_erases requireIdleDevicePrefix_erases)
      Noise.PendingScheduler.requireIdleDevice_store
  · exact old_store safe transport _ _ (RxHistory.audit_erases (erasesPrefix_lift _))
      requireNoCryptWork_sameKernel
  · intro t
    exact old_store safe transport _ _ (RxHistory.audit_erases (erasesPrefix_lift _))
      (timerWorker_sameKernel t)
  · intro ticks
    exact old_store safe transport _ _ (RxHistory.audit_erases (advanceAudit_erases ticks))
      (advance_sameKernel ticks)
end Leanux.Proofs.WG.TimerDiscipline.HookState
