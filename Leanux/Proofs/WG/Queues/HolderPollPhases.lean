import Leanux.Proofs.WG.Queues.HolderPollFrames

/-! Existing stable source-phase contracts carry the complete durable-holder
account when the phase has no acquisition or durable-holder debit. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open RxJoint PollCarrier

theorem peek_accounted (initial : Ledger) (loans : Reservations) (pid : PeerId) :
    PrefixEnsures (Accounted (StableBoundary initial) loans) (fun _ => True)
      (access (liftWGObserver (peekAccess pid)))
      (fun first => Accounted (fun ls h w => AfterPeek initial ls pid first h w ∧
        StableAt initial h w ∧ HeadAt pid first w) loans) := by
  apply accounted_rule _ (liftWG (peekRxQueue pid)) id (access_appends _)
    (access_erases (liftWGObserver_erases (peekAccess_erases pid))).to_projected
    (fun ls => stable_peek_observed initial ls pid)
  intro w x v run
  exact native_frame _ (peek_frame pid) w v x run

theorem ready_accounted (initial : Ledger) (loans : Reservations) (pid : PeerId)
    (first : Option SkbId) :
    PrefixEnsures
      (Accounted (fun ls h w => AfterPeek initial ls pid first h w ∧
        StableAt initial h w ∧ HeadAt pid first w) loans) (fun _ => True)
      (access (liftWGObserver (readyAccess first)))
      (fun go => Accounted (fun ls h w => AfterPeek initial ls pid first h w ∧ StableAt initial h w ∧
        (go = false → ColdHead pid w.wg) ∧ (go = true → ReadyPacket first w)) loans) := by
  apply accounted_rule _ _ id (access_appends _)
    (access_erases (liftWGObserver_erases (readyAccess_erases first))).to_projected
    (fun ls => stable_ready_observed initial ls pid first)
  intro w x v run
  have same := (ready_result first w.wg v.wg x w.ambient v.ambient
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) _ w v x run)).1
  rw [same]
  exact Frame.refl _

theorem capture_accounted (initial : Ledger) (loans : Reservations) (pid skb : Nat) :
    PrefixEnsures
      (Accounted (fun ls h w => AfterPeek initial ls pid (some skb) h w ∧
        StableAt initial h w ∧ ReadyPacket (some skb) w) loans) (fun _ => True) (capture skb)
      (fun out => Accounted (fun ls h w => Captured initial ls pid skb out h w ∧
        StableAt initial h w ∧ out.1.state ≠ .uncrypted) loans) := by
  apply accounted_observer _ (capture_appends skb)
    (fun ls => stable_capture_observed initial ls pid skb)
  intro w h out v run
  rw [(RxDisposition.capture_selected skb w v h out.1 out.2 run).1]
  exact Frame.refl _

theorem drop_accounted (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ready : pkt.state ≠ .uncrypted) :
    PrefixEnsures
      (Accounted (fun ls h w => Captured initial ls pid skb (pkt,stamp) h w ∧ StableAt initial h w) loans)
      (fun _ => True) (RxJoint.drop pid n skb stamp)
      (fun _ => Accounted (fun ls h w => Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w) loans) := by
  have erases : ErasesPrefix (RxJoint.drop pid n skb stamp) (liftWG (dropRxQueue pid)) := by
    unfold RxJoint.drop
    simpa only [bind_pure_unit,dropRxQueue] using erasesPrefix_bind
      (access_erases (liftWGObserver_erases (rxDropPeekedPrefix_erases pid)))
      (fun _ => erasesPrefix_emit _)
  apply accounted_rule _ _ id ((access_appends _).bind (fun _ => emit_appends _))
    erases.to_projected (fun ls => stable_drop_observed initial ls pid n skb stamp pkt ready)
  intro w x v run
  exact native_frame _ (drop_frame pid) w v x run

theorem complete_accounted (initial : Ledger) (loans : Reservations) (pid : PeerId) :
    PrefixEnsures
      (Accounted (fun ls h w => Ready initial ls h w ∧ StableAt initial h w ∧ ColdHead pid w.wg) loans)
      (fun _ => True) (access (liftWGObserver (completeAccess pid)))
      (fun _ => Accounted (StableBoundary initial) loans) := by
  apply accounted_rule _ _ id (access_appends _)
    (access_erases (liftWGObserver_erases (completeAccess_erases pid))).to_projected
    (fun ls => stable_complete_observed initial ls pid)
  intro w x v run
  exact native_frame _ (complete_frame pid) w v x run

theorem product_frame (a : Leanux.M α) (frame : SameProductStore a)
    (w v : World) (x : α) (run : a.run w = .ok (x,v)) : Frame w.wg v.wg := by
  apply Frame.of_store
  exact (ProjectedAction.iff_run _ _ _).mp
    (frame.factor (fun s : ProductStore43 => s.2.2.2)) w x v run

theorem lift_accounted {P : Reservations → List RxJoint.Event → World → Prop} (a : Leanux.M α) (frame : SameProductStore a)
    (old : ∀ ls, PrefixPreserves (P ls) (fun _ => True) (liftPrefix a)) (loans : Reservations) :
    PrefixPreserves (Accounted (fun ls h w => P ls h w ∧ StableAt initial h w) loans)
      (fun _ => True) (liftPrefix a) := by
  unfold PrefixPreserves
  apply accounted_rule
    (P := fun ls h w => P ls h w ∧ StableAt initial h w)
    (Q := fun ls _ h w => P ls h w ∧ StableAt initial h w) _ a id (Appends.lift _) (erasesPrefix_lift _).to_projected
    (fun ls => stable_lift_observed (initial := initial) a frame (old ls))
  intro w x v run
  exact product_frame a frame w v x run

theorem receipt_lift_accounted {P : Reservations → List RxJoint.Event → World → Prop} (a : Leanux.M α) (frame : SameProductStore a)
    (f : RunWitness α → RxJoint.Event) (hf : ∀r,removedStamp (f r) = none)
    (old : ∀ ls, PrefixPreserves (P ls) (fun _ => True) (receiptObserved (liftPrefix a) f))
    (loans : Reservations) :
    PrefixPreserves (Accounted (fun ls h w => P ls h w ∧ StableAt initial h w) loans)
      (fun _ => True) (receiptObserved (liftPrefix a) f) := by
  unfold PrefixPreserves
  apply accounted_rule
    (P := fun ls h w => P ls h w ∧ StableAt initial h w)
    (Q := fun ls _ h w => P ls h w ∧ StableAt initial h w) _ a id (Appends.lift _).receiptObserved
    (RxLink.receipt_erases (erasesPrefix_lift _)).to_projected
    (fun ls => stable_receipt_lift_observed (initial := initial) a frame f hf (old ls))
  intro w x v run
  exact product_frame a frame w v x run

theorem counter_accounted (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves
      (Accounted (fun ls h w => Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w) loans)
      (fun _ => True)
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (RxJoint.Event.checkedCounter n skb stamp pkt)) := by
  unfold PrefixPreserves
  apply accounted_rule
    (P := fun ls h w => Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w)
    (Q := fun ls _ h w => Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w)
    (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
      (RxJoint.Event.checkedCounter n skb stamp pkt))
    (liftWG (counterValidate pkt.keypair pkt.nonce)) id (access_appends _).receiptObserved
    (RxLink.receipt_erases (access_erases (liftWGObserver_erases (counterValidatePrefix_erases _ _)))).to_projected
    (fun ls => stable_live_counter initial ls pid n skb stamp pkt)
  intro w x v run
  exact native_frame _ (counter_frame pkt.keypair pkt.nonce) w v x run

theorem cleanup_accounted (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer = pid) :
    PrefixEnsures
      (Accounted (fun ls h w => Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans)
      (fun _ => True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb)))
      (fun _ => Accounted (StableBoundary initial) loans) := by
  have he : ErasesPrefix
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))) (liftWG (cleanup skb pkt flag)) := by
    rw [cleanup_poll_guard skb pkt pid flag guard]
    simp only [liftWG_bind]
    exact erasesPrefix_bind (access_erases (liftWGObserver_erases (keypairPutPrefix_erases _ _))) (fun _ =>
      erasesPrefix_bind (access_erases (liftWGObserver_erases (peerPutMixed_erases _))) (fun _ =>
      erasesPrefix_bind (erasesPrefix_lift _) (fun _ => access_erases (liftWGObserver_erases (freeRxSkbPrefix_erases _)))))
  apply accounted_rule _ _ id ((access_appends _).bind (fun _ =>
    (access_appends _).bind (fun _ => (Appends.lift _).bind (fun _ => access_appends _))))
    he.to_projected (fun ls => stable_cleanup_observed initial ls pid skb stamp pkt flag guard)
  intro w x v run
  exact native_frame _ (cleanup_frame skb pkt flag) w v x run

theorem cleanup_accounted_bind (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer = pid) (tail : Obs α)
    (next : PrefixEnsures (Accounted (StableBoundary initial) loans) (fun _ => True) tail Q) :
    PrefixEnsures
      (Accounted (fun ls h w => Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans)
      (fun _ => True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q := by
  simpa only [bind_assoc] using PrefixEnsures.bind
    (cleanup_accounted initial loans pid skb stamp pkt flag guard) (fun u => by cases u; exact next)

theorem cleanup_live_accounted_bind (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer = pid) (tail : Obs α)
    (next : PrefixEnsures (Accounted (StableBoundary initial) loans) (fun _ => True) tail Q) :
    PrefixEnsures
      (Accounted (fun ls h w => Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w) loans)
      (fun _ => True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q :=
  (cleanup_accounted_bind initial loans pid skb stamp pkt flag guard tail next).consequence
    (fun _ _ ⟨holders,aligned,hi,stable⟩ => ⟨holders,aligned,hi.1,stable⟩) (fun _ _ _ hi => hi)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
