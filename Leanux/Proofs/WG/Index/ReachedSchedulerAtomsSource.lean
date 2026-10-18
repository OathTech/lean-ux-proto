import Leanux.Proofs.WG.Index.ReachedSchedulerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedScheduler
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem observed_store {α : Type} (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (observed : RxHistory.Obs α) (action : Leanux.M α)
    (account : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe observed)
    (erase : ErasesPrefix observed action) (frame : SameProductStore action) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe observed := by
  apply Reached.aux_pair _ initial loans before account
  intro w h pre result v run
  have same := (ProjectedAction.iff_run _ _ _).mp frame w result v
    ((erase w h).symm.trans run)
  exact (Reached.aux_store same pre).2

theorem atoms (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    RxHistory.SchedulerSource.AtomContracts
      (Reached.Aux initial loans before) OwnerChecks.Safe (fun {_} g=>g) := by
  have account := HolderAuxScheduler.atoms initial loans before
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact observed_store initial loans before _ _ (account.ambient a)
      (RxHistory.mixed_erases (erasesPrefix_lift _))
      (fun _=>productAmbient_spec a _ (fun _ _ pre=>pre))
  · intro α e
    exact observed_store initial loans before _ _ (account.stopped e)
      (RxHistory.mixed_erases (erasesPrefix_throw e)) (fun _=>hoare_throw e)
  · intro pid
    apply observed_store initial loans before _ _ (account.peer pid)
      (RxHistory.mixed_erases (liftWGObserver_erases (getPeerMixed_erases pid)))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (getPeer_normal pid w v p a b run).1
  · intro id
    apply observed_store initial loans before _ _ (account.packet id)
      (RxHistory.mixed_erases (liftWGObserver_erases (getTxSkbPrefix_erases id)))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (Packets.getTxSkb_current id w v p a b run).1
  · intro f
    apply Reached.aux_pair _ initial loans before (account.work f)
    intro w h pre result v run
    have native := DecryptIteration.native_normal
      (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _))) (Prod.ext run rfl)
    have fields := (ProjectedAction.iff_run_ambient _ _ _).mp (work_fields f)
      w.wg w.ambient result v.wg v.ambient native
    exact ⟨BaseCoherence.transport pre.2.1 (congrArg Prod.fst fields),
      ConfigurationIndex.fields_core w.wg v.wg (congrArg Prod.snd fields) pre.2.2⟩
  · intro a
    exact observed_store initial loans before _ _ (account.occupancy a)
      (RxHistory.mixed_erases (activationOccupancyPrefix_erases a)) (activationOccupancy_sameKernel a)
  · intro next
    exact observed_store initial loans before _ _ (account.pending next)
      (RxHistory.mixed_erases (pendingNapiPrefix_erases next)) (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact observed_store initial loans before _ _ (account.hasWork a)
      (RxHistory.mixed_erases (activationHasWorkPrefix_erases a)) (activationHasWork_sameKernel a)
  · apply observed_store initial loans before _ _ account.trial
      (RxHistory.audit_erases consistentFilterAudit_erases)
    exact (show SameProductStore getAmbient from fun _=>
      productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ pre=>pre)).bind
      (fun w=>filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)

end Leanux.Proofs.WG.Index.ReachedScheduler
