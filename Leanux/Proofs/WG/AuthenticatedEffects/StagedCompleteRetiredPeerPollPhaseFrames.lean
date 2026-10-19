import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollSelectionFrames

/-! Native-neutral poll checks and the literal selected-cell cleanup retain
the exact phase account and the unchanged removal history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders RxJoint PollCarrier

theorem context_store (action : Obs α) (original : Leanux.M β) (project : α → β)
    (appends : Appends action) (erase : ErasesTo project action original)
    (quiet : HistoryFrame removedStamp action) (same : SameProductStore original)
    (front initial : RxCredits.Ledger) (loans : Reservations) :
    PrefixPreserves (Context front initial loans) (fun _ => True) action := by
  apply PollCarrier.normal_spec appends
  intro w h x v before run
  have native : original.run w = .ok (project x,v) := by rw [←erase w h,run]; rfl
  exact before.store (congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp same w (project x) v native)) (removed_frame quiet w h)

theorem context_lift (front initial : RxCredits.Ledger) (loans : Reservations)
    (action : Leanux.M α) (same : SameProductStore action) :
    PrefixPreserves (Context front initial loans) (fun _ => True) (liftPrefix action) :=
  context_store _ _ id (Appends.lift _) (erasesPrefix_lift _).to_projected (HistoryFrame.lift _ _) same front initial loans

theorem bare_observed (action : Obs α) (appends : Appends action)
    (keeps : ∀ front initial loans, PrefixPreserves (Context front initial loans) (fun _ => True) action) :
    PrefixPreserves (Bare initial loans pid skb stamp) (fun _ => True) action := by
  apply PollCarrier.normal_spec appends
  intro w h x v before run
  obtain ⟨owner,slot,stampSlot,account⟩ := before
  have post := (keeps [Selected stamp owner] initial loans w h account).choose_spec.2.2
  rw [run] at post
  exact ⟨owner,slot,stampSlot,post⟩

theorem live_observed (action : Obs α) (original : Leanux.M α) (appends : Appends action)
    (erase : ErasesPrefix action original)
    (keeps : ∀ front initial loans, PrefixPreserves (Context front initial loans) (fun _ => True) action)
    (cells : SameView RxDisposition.rxStore original) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _ => True) action := by
  apply PollCarrier.normal_spec appends
  intro w h x v before run
  have post := (bare_observed action appends keeps w h before.1).choose_spec.2.2
  rw [run] at post
  exact ⟨post,RxDisposition.selected_transport skb stamp pkt w v
    ((ProjectedAction.iff_run _ _ _).mp cells w x v ((erase w h).symm.trans run)) before.2⟩

theorem live_lift (action : Leanux.M α) (same : SameProductStore action) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _ => True) (liftPrefix action) :=
  live_observed _ _ (Appends.lift _) (erasesPrefix_lift _)
    (fun _ _ _ => context_lift _ _ _ _ same) (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v run
      have device := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
        ((ProjectedAction.iff_run _ _ _).mp same w x v run)
      change v.wg.dev = w.wg.dev at device
      unfold RxDisposition.rxStore RxDisposition.nativeRxStore
      rw [device])

theorem live_receipt_lift (action : Leanux.M α) (same : SameProductStore action)
    (f : RunWitness α → RxJoint.Event) (quiet : ∀ r, removedStamp (f r) = none) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _ => True)
      (receiptObserved (liftPrefix action) f) :=
  live_observed _ _ (Appends.lift _).receiptObserved (RxLink.receipt_erases (erasesPrefix_lift _))
    (fun front initial loans => context_store _ _ id (Appends.lift _).receiptObserved
      (RxLink.receipt_erases (erasesPrefix_lift _)).to_projected
      ((HistoryFrame.lift _ _).receiptObserved quiet) same front initial loans) (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v run
      have device := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
        ((ProjectedAction.iff_run _ _ _).mp same w x v run)
      change v.wg.dev = w.wg.dev at device
      unfold RxDisposition.rxStore RxDisposition.nativeRxStore
      rw [device])

theorem context_counter (front initial : RxCredits.Ledger) (loans : Reservations)
    (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Context front initial loans) (fun _ => True)
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (RxJoint.Event.checkedCounter n skb stamp pkt)) := by
  apply PollCarrier.normal_spec (access_appends _).receiptObserved
  intro w h x v before run
  obtain ⟨holders,account,stable⟩ := before
  have erase := RxLink.receipt_erases (f := RxJoint.Event.checkedCounter n skb stamp pkt)
    (access_erases (liftWGObserver_erases (counterValidatePrefix_erases pkt.keypair pkt.nonce)))
  have original := (erase w h).symm.trans run
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    _ w v x original
  obtain ⟨after,ready⟩ := account.counter stable pkt.keypair pkt.nonce w.ambient v.ambient native
  have quiet := removed_frame ((access_removed (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce))).receiptObserved
    (fun (r : RunWitness Bool) => (rfl : removedStamp (RxJoint.Event.checkedCounter n skb stamp pkt r) = none))) w h
  refine ⟨holders,?_,?_⟩
  · change Phased _ (front ++ remaining initial _) loans v.wg
    rw [quiet]
    exact after
  · change StableRx (remaining initial _) v.wg
    rw [quiet]
    exact ready

theorem live_counter (initial : RxCredits.Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _ => True)
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (RxJoint.Event.checkedCounter n skb stamp pkt)) :=
  live_observed _ _ (access_appends _).receiptObserved
    (RxLink.receipt_erases (access_erases (liftWGObserver_erases (counterValidatePrefix_erases _ _))))
    (fun front initial loans => context_counter front initial loans n skb stamp pkt) (RxDisposition.counter_rxStore _ _)

theorem cleanup (initial : RxCredits.Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer = pid) :
    PrefixEnsures (Bare initial loans pid skb stamp) (fun _ => True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb)))
      (fun _ => Boundary initial loans) := by
  let action : Obs Unit := do
    access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
    access (liftWGObserver (peerPutMixed (some pid)))
    _ ← liftPrefix (branch .rxPollFree flag)
    access (liftWGObserver (freeRxSkbPrefix skb))
  have erase : ErasesPrefix action (liftWG (RxCredits.cleanup skb pkt flag)) := by
    rw [cleanup_poll_guard skb pkt pid flag guard]
    simp only [liftWG_bind]
    exact erasesPrefix_bind (access_erases (liftWGObserver_erases (keypairPutPrefix_erases _ _))) (fun _ =>
      erasesPrefix_bind (access_erases (liftWGObserver_erases (peerPutMixed_erases _))) (fun _ =>
      erasesPrefix_bind (erasesPrefix_lift _) (fun _ => access_erases (liftWGObserver_erases (freeRxSkbPrefix_erases _)))))
  have appends : Appends action := (access_appends _).bind (fun _ =>
    (access_appends _).bind (fun _ => (Appends.lift _).bind (fun _ => access_appends _)))
  have quiet : HistoryFrame removedStamp action := (access_removed _).bind (fun _ =>
    (access_removed _).bind (fun _ => (HistoryFrame.lift _ _).bind (fun _ => access_removed _)))
  apply PollCarrier.normal_spec appends
  intro w h result v before run
  cases result
  obtain ⟨owner,ownerSlot,stampSlot,holders,account,stable⟩ := before
  have original := (erase w h).symm.trans run
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    _ w v () original
  have slot : (Selected stamp owner).packet.slot = skb := by simp [Selected,packetOfStamp,stampSlot]
  obtain ⟨after,_⟩ := account.cleanup stable rfl (guard.trans ownerSlot.symm) w.ambient v.ambient (slot ▸ native)
  have history := removed_frame quiet w h
  refine ⟨holders,?_,?_⟩
  · change Phased _ ([] ++ remaining initial _) loans v.wg
    rw [history]
    exact after.phased
  · change StableRx (remaining initial _) v.wg
    rw [history]
    exact after.stable

theorem complete (initial : RxCredits.Ledger) (loans : Reservations) (pid : PeerId) :
    PrefixEnsures (fun h w => Boundary initial loans h w ∧ ColdHead pid w.wg) (fun _ => True)
      (access (liftWGObserver (completeAccess pid))) (fun _ => Boundary initial loans) := by
  apply PollCarrier.normal_spec (access_appends _)
  intro w h result v before run
  cases result
  obtain ⟨holders,account⟩ := before.1.exact
  have original := (access_erases (liftWGObserver_erases (completeAccess_erases pid)) w h).symm.trans run
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    _ w v () original
  have after := account.rx_complete before.2 w.ambient v.ambient native
  have history := removed_frame (access_removed (liftWGObserver (completeAccess pid))) w h
  refine ⟨holders,?_,?_⟩
  · change Phased _ ([] ++ remaining initial _) loans v.wg
    rw [history]
    exact after.phased
  · change StableRx (remaining initial _) v.wg
    rw [history]
    exact after.stable

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
