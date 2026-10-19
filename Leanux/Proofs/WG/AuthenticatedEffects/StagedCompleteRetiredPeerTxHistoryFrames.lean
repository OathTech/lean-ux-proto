import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxStepFrames
import Leanux.Proofs.WG.Queues.HolderTxHistory

/-! The actual TX iteration and its existing lifetime observer retain the
fixed RX removal cut and the same-holder exact account. This does not invent
an RX event for a TX queue alias or infer stopped endpoint ownership. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits DurableHolders

theorem ExactBoundary.lift (action : WG.M α)
    (keeps : Preserves (ExactBoundary carriers loans) action) :
    Preserves (fun w : World => ExactBoundary carriers loans w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v account run
  exact (hoare_iff_run_ambient _ _ _).mp keeps w.wg w.ambient x v.wg v.ambient account
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
      action w v x run)

theorem ExactBoundary.product_frame (action : Leanux.M α) (frame : SameProductStore action) :
    Preserves (fun w : World => ExactBoundary carriers loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v account run
  exact account.store (congrArg (fun p : ProductStore43 => p.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w x v run))

theorem ExactBoundary.tx_iteration (pid : PeerId) :
    Preserves (fun w : World => ExactBoundary carriers loans w.wg)
      (WG.txIter pid (Env.condResched .txWorker)) := by
  unfold WG.txIter workerIter
  apply preserves_bind (ExactBoundary.lift _ (ExactBoundary.tx_step pid))
  intro more
  split
  · exact preserves_pure _
  · apply preserves_bind
    · apply preserves_bind (ExactBoundary.product_frame _ (condResched_sameKernel .txWorker))
      intro need
      exact productAmbient_spec (AmbientM.branch .txNeedResched need) _ (fun _ _ hi => hi)
    · intro yielded
      split <;> exact preserves_pure _

/-- The mixed observer changes only the lifetime portion of the existing
receive journal. Its actual native endpoint supplies the new exact account. -/
theorem ExactAt.mixed (action : PrefixM LifetimeEvent α) (original : Leanux.M α)
    (erases : ErasesPrefix action original)
    (keeps : ∀ carriers, Preserves (fun w : World => ExactBoundary carriers loans w.wg) original) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) (RxHistory.mixed action) := by
  apply NapiCarrier.normal_spec (Appends.focus _ _ _)
  intro w h result v account run
  obtain ⟨old,history,account⟩ := account
  have actual : original.run w = .ok (result,v) :=
    (RxHistory.mixed_erases erases w h).symm.trans run
  have after := (hoare_iff_run _ _ _).mp (keeps _) w result v account actual
  obtain ⟨extra,extended⟩ := (Appends.focus RxHistory.Event.audit RxHistory.auditEvent (auditFocus action)) w h
  change (runPrefix (RxHistory.mixed action) w h).2 = h ++ extra at extended
  have quiet : NapiCarrier.removedPackets (runPrefix (RxHistory.mixed action) w h).2 =
      NapiCarrier.removedPackets h := by
    exact focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent NapiCarrier.removed
      (fun _ => rfl) (auditFocus action) w h
  have empty : NapiCarrier.removedPackets extra = [] := by
    rw [extended] at quiet
    exact List.append_cancel_left (by
      simpa only [NapiCarrier.removedPackets,List.filterMap_append,List.append_nil] using quiet)
  refine ⟨old ++ extra,?_,?_⟩
  · change (runPrefix (RxHistory.mixed action) w h).2 = before ++ (old ++ extra)
    rw [extended,history,List.append_assoc]
  simp only [NapiCarrier.removedPackets,List.filterMap_append]
  change ExactBoundary (remaining initial (NapiCarrier.removedPackets old ++ NapiCarrier.removedPackets extra)) loans v.wg
  rw [empty,List.append_nil]
  exact after

theorem ExactAt.tx_iteration (initial : RxCredits.Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  ExactAt.mixed _ _ (txIterPrefix_erases pid (erasesPrefix_lift _))
    (fun _ => ExactBoundary.tx_iteration pid)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
