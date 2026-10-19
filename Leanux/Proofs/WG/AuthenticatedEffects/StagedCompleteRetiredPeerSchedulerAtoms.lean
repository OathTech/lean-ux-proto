import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAuxiliary
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxHistoryFrames
import Leanux.Proofs.WG.Queues.HolderAuxScheduler

/-! Each original scheduler atom transports the exact account, including
work-queue updates and the copied consistency trial. The existing auxiliary
proof and the new account share the identical observer action. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits Auxiliary

private theorem stored (g : PrefixM LifetimeEvent α) (original : Leanux.M α)
    (erase : ErasesPrefix g original) (frame : SameProductStore original) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) (RxHistory.mixed g) :=
  ExactAt.mixed _ _ erase (fun _ => ExactBoundary.product_frame original frame)

theorem exact_atoms (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    RxHistory.SchedulerSource.AtomContracts (ExactAt initial loans before) (fun _ => True)
      (fun {_} g => g) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact stored _ _ (erasesPrefix_lift _) (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))
  · intro α e
    exact stored _ _ (erasesPrefix_throw e) (fun _ => hoare_throw e)
  · intro pid
    apply stored _ _ (liftWGObserver_erases (getPeerMixed_erases pid))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (getPeer_normal pid w v p a b run).1
  · intro id
    apply stored _ _ (liftWGObserver_erases (getTxSkbPrefix_erases id))
    apply liftWG_sameProductStore
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (Packets.getTxSkb_current id w v p a b run).1
  · intro f
    exact ExactAt.mixed _ _ (liftWGObserver_erases (erasesStatePrefix_lift _))
      (fun _ => ExactBoundary.lift _ (ExactBoundary.native_fields (HolderTxHistory.work_fields f)))
  · intro a
    exact stored _ _ (activationOccupancyPrefix_erases a) (activationOccupancy_sameKernel a)
  · intro next
    exact stored _ _ (pendingNapiPrefix_erases next) (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact stored _ _ (activationHasWorkPrefix_erases a) (activationHasWork_sameKernel a)
  · have frame : SameProductStore (do
        let w ← getAmbient
        w.suspended.filterM Env.Activation.consistent) :=
      (show SameProductStore getAmbient from fun _ =>
        productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)).bind
        (fun w => filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)
    exact TimerEnvironment.audit_at _ _ consistentFilterAudit_erases
      (fun _ => ExactBoundary.product_frame _ frame)

theorem atoms (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    RxHistory.SchedulerSource.AtomContracts (Inv initial loans before) OwnerChecks.Safe
      (fun {_} g => g) := by
  have old := HolderAuxScheduler.atoms initial loans before
  have exactAccount := exact_atoms initial loans before
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a; exact pair_preserves _ (old.ambient a) (exactAccount.ambient a)
  · intro α e; exact pair_preserves _ (old.stopped e) (exactAccount.stopped e)
  · intro pid; exact pair_preserves _ (old.peer pid) (exactAccount.peer pid)
  · intro id; exact pair_preserves _ (old.packet id) (exactAccount.packet id)
  · intro f; exact pair_preserves _ (old.work f) (exactAccount.work f)
  · intro a; exact pair_preserves _ (old.occupancy a) (exactAccount.occupancy a)
  · intro next; exact pair_preserves _ (old.pending next) (exactAccount.pending next)
  · intro a; exact pair_preserves _ (old.hasWork a) (exactAccount.hasWork a)
  · exact pair_preserves _ old.trial exactAccount.trial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Scheduler
