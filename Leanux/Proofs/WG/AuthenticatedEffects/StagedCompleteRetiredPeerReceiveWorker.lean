import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeDispatch
import Leanux.Proofs.WG.Queues.HandshakeWorker

/-! The unchanged handshake worker transports exact reference accounts over
the original receive-removal history. Normal endpoints use the same actual
source run; stopped runs retain the original event prefix and native error. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

private theorem install (ring : PtrRing (List UInt8 × SkbSource)) :
    Preserves (Input cs loans) (modifyDev fun d => {d with handshakeQueue:=ring}) := by
  apply join
  · apply boundary
    intro holders
    apply device
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd : w.dev <;> simp [hd,rxView]
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine)
    · apply (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.modifyDevice)
      all_goals intro d; rfl
    · apply CurrentSlots.fields_preserves (project := id)
      intro initial
      change Preserves (fun w => CurrentSlots.fields w = initial) _
      slot_fields_step initial

private theorem decrement : Preserves (ExactBoundary cs loans)
    (modifyDev fun d => {d with handshakeQueueLen:=d.handshakeQueueLen-1}) := by
  apply boundary
  intro holders
  apply device
  intro w
  unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  cases hd : w.dev <;> simp [hd,rxView]

/-- Empty polls return normally without acquiring a peer. A consumed packet
runs the unchanged receiver with the account and auxiliary input intact. -/
theorem native_step : Hoare WG.receiveStep (Input cs loans) (fun _ => ExactBoundary cs loans) := by
  unfold WG.receiveStep
  apply hoare_bind _ _
    (input_store getDev_sameWGStore)
  intro d
  cases outcome : d.handshakeQueue.consume with
  | mk item ring =>
    cases item with
    | none =>
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .workerConsumed false) (Input cs loans))
      intro _
      apply hoare_consequence (hoare_pure false (Input cs loans))
      · exact fun _ hi => hi
      · exact fun _ _ hi => hi.2.1
    | some item =>
      obtain ⟨msg,src⟩ := item
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .workerConsumed true) (Input cs loans))
      intro _
      apply hoare_bind _ _ (install ring)
      intro _
      apply hoare_bind _ _ (receive msg src)
      intro _
      exact preserves_bind decrement (fun _ => preserves_pure true)

private theorem quiet_cut {action : RxHistory.Obs α} (ha : Appends action)
    (quiet : HistoryFrame NapiCarrier.removed action) (history : h = before ++ old)
    (run : runPrefix action w h = (.ok (x,v),k))
    (post : ExactBoundary (remaining initial (NapiCarrier.removedPackets old)) loans v.wg) :
    ExactAt initial loans before k v := by
  obtain ⟨extra,extraEq⟩ := ha w h
  have tail : k = h ++ extra := by simpa only [run] using extraEq
  have empty : NapiCarrier.removedPackets extra = [] := by
    have same := quiet w h
    change NapiCarrier.removedPackets (runPrefix action w h).2 = NapiCarrier.removedPackets h at same
    rw [extraEq] at same
    exact List.append_cancel_left (by simpa only [NapiCarrier.removedPackets,List.filterMap_append,List.append_nil] using same)
  refine ⟨old ++ extra,by rw [tail,history,List.append_assoc],?_⟩
  simp only [NapiCarrier.removedPackets,List.filterMap_append]
  change ExactBoundary (remaining initial (NapiCarrier.removedPackets old ++ NapiCarrier.removedPackets extra)) loans v.wg
  rw [empty,List.append_nil]
  exact post

/-- Exact normal accounts are transported on the original observer's fixed
RX residual, without selecting a second funding witness or history. -/
theorem step_normal (account : ExactAt initial loans before h w)
    (entry : HandshakeEntry.Entry w.wg)
    (run : runPrefix Origins.HistoryAdapters.receiveStep w h = (.ok (result,v),k)) :
    ExactAt initial loans before k v := by
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    WG.receiveStep w v result
    ((Origins.HistoryAdapters.receiveStep_erases w h).symm.trans (congrArg Prod.fst run))
  obtain ⟨old,history,account⟩ := account
  have post := (hoare_iff_run_ambient _ _ _).mp native_step
    w.wg w.ambient result v.wg v.ambient ⟨account,entry⟩ native
  exact quiet_cut (Appends.focus _ _ _) HandshakeWorker.step_quiet history run post

/-- Rescheduling preserves the same account at every normal iteration
endpoint, including normal worker exhaustion and yield. -/
theorem iteration_normal (account : ExactAt initial loans before h w)
    (entry : HandshakeEntry.Entry w.wg)
    (run : runPrefix Origins.HistoryAdapters.receiveIteration w h = (.ok (result,v),k)) :
    ExactAt initial loans before k v := by
  unfold Origins.HistoryAdapters.receiveIteration workerIterPrefix at run
  obtain ⟨more,u,j,step,tail⟩ := DecryptIteration.bind_normal run
  have post := step_normal account entry step
  cases more with
  | false =>
    simp only [Bool.not_false,ite_true] at tail
    cases tail
    exact post
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨yielded,z,l,reschedule,done⟩ := DecryptIteration.bind_normal tail
    cases done
    simp only [runPrefix_lift,Prod.mk.injEq] at reschedule
    obtain ⟨actual,rfl⟩ := reschedule
    exact post.store ((ProjectedAction.iff_run _ _ _).mp
      (condResched_sameKernel .receiveWorker) u yielded _ actual)

/-- Source entry support is obtained from the very same owner journal and
slot carrier that accompany the existing initialized scheduler. -/
theorem iteration_owner (account : ExactAt initial loans before h w)
    (owner : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg)
    (run : runPrefix Origins.HistoryAdapters.receiveIteration w h = (.ok (result,v),k)) :
    ExactAt initial loans before k v :=
  iteration_normal account (HandshakeEntry.of_owner owner slots) run

/-- The old observer's native result, including an error, remains unchanged.
Its actual history never removes an RX carrier during a handshake step. -/
theorem step_source (w : World) (h : List RxHistory.Event) :
    (runPrefix Origins.HistoryAdapters.receiveStep w h).1 = (liftWG WG.receiveStep).run w ∧
      (∃ suffix, (runPrefix Origins.HistoryAdapters.receiveStep w h).2 = h ++ suffix) ∧
      NapiCarrier.removedPackets (runPrefix Origins.HistoryAdapters.receiveStep w h).2 =
        NapiCarrier.removedPackets h := by
  exact ⟨Origins.HistoryAdapters.receiveStep_erases w h,
    Appends.focus _ _ _ w h,HandshakeWorker.step_quiet w h⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
