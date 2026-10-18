import Leanux.Proofs.WG.HandshakeSecurity.ResponderGlobalHistory

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Global
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

theorem store (h : List RxHistory.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (entry : Inv h w) : Inv h v := by
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  refine ⟨⟨Authorized.frame entry.1.1 ?_, CurrentSlots.fields_transport entry.1.2 ?_⟩, entry.2⟩
  · unfold current
    rw [device]
  · unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]

theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) : Preserves (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.2) store frame

theorem quiet (g : RxHistory.Obs α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a) (frame : HistoryFrame consumer g)
    (preserves : ∀ confirmed, Framing.Preserves (fun w : World => History.Native confirmed w.wg) a) :
    Preserves g := by
  intro w h hi
  obtain ⟨suffix, appends⟩ := appends w h
  have same := frame w h
  have empty : suffix.filterMap consumer = [] := by
    rw [appends, List.filterMap_append] at same
    simpa using same
  have safe : Safe (runPrefix g w h).2 := appends ▸ hi.2.quiet empty
  have labelFrame : Confirmation.completedLabels (runPrefix g w h).2 = Confirmation.completedLabels h := by
    rw [labels_consumer, labels_consumer, frame w h]
  refine ⟨suffix, appends, safe, ?_⟩
  cases run : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    refine ⟨?_, safe⟩
    rw [labelFrame]
    exact (hoare_iff_run _ _ _).mp (preserves _) w out.1 out.2 hi.1
      ((erases w h).symm.trans run)

theorem native_mixed (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (erases : ErasesStatePrefix g a)
    (preserves : ∀ confirmed, Framing.Preserves (History.Native confirmed) a) :
    Preserves (RxHistory.mixed (liftWGObserver g)) :=
  quiet _ (liftWG a) (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases erases))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      consumer (fun _ => rfl) _)
    (fun confirmed => PublicationPoll.native_product _ _ (preserves confirmed))

theorem mixed (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (preserves : ∀ confirmed, Framing.Preserves (fun w : World => History.Native confirmed w.wg) a) :
    Preserves (RxHistory.mixed g) :=
  quiet _ a (Appends.focus _ _ _) (RxHistory.mixed_erases erases)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      consumer (fun _ => rfl) _) preserves

theorem pending : Preserves (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply native_mixed _ RxNapi.pendingSource RxNapi.pending_erases
  intro confirmed
  unfold RxNapi.pendingSource
  exact preserves_bind (native_store getDev_sameWGStore confirmed) (fun _ => preserves_pure _)

theorem scheduled : Preserves (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply native_mixed _ RxNapi.scheduledSource RxNapi.scheduled_erases
  intro confirmed
  unfold RxNapi.scheduledSource
  exact preserves_bind (native_store getDev_sameWGStore confirmed) (fun _ => preserves_pure _)

theorem napiSoftirq (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) :
    Preserves RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.2) store pending (observePoll H1 slots)

theorem pollScheduledInline (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) :
    Preserves RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ hi => hi.2) store pending (observePoll H1 slots)

theorem napiIrqExit (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) :
    Preserves RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.2) store scheduled (napiSoftirq H1 slots)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Global
