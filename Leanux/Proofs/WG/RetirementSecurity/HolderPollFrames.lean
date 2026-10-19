import Leanux.Proofs.WG.RetirementSecurity.HolderPollCallbacks

/-! History-quiet product bookkeeping keeps the poll's independent support
and its exact selected key credit. These are frames around the original
ambient/endpoint operations; no semantic callback is covered by a frame. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open RxJoint PollCarrier DurableHolders

theorem support_store (before : Support sessions locals active w)
    (same : wgStoreView v=wgStoreView w) : Support sessions locals active v := by
  have device : v.dev=w.dev := congrArg WGStoreView.dev same
  refine ⟨OccurrenceStack.ready_store same before.1,⟨?_,?_⟩,?_,?_⟩
  · intro s found
    exact before.2.1.1 s (by simpa only [ConfiguredIdentity.view,device] using found)
  · intro d found slot key resident valid
    exact before.2.1.2 d (device.symm.trans found) slot key resident valid
  · apply BaseCoherence.transport before.2.2.1
    simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,device]
  · apply KeySlotLiveness.transport before.2.2.2
    funext pid
    simp only [KeySlotLiveness.view,peerAt,device]

theorem keys_store (before : HolderAccount temporary w)
    (same : wgStoreView v=wgStoreView w) : HolderAccount temporary v := by
  have device : v.dev=w.dev := congrArg WGStoreView.dev same
  apply before.points
  unfold ownershipPointView ownershipAt peerAt keyReferenceView keyAt packetKeyWords
  rw [device]

theorem product_store {action : Leanux.M α} (same : SameProductStore action)
    (before : HolderAccount temporary w.wg ∧ Support sessions locals active w.wg)
    (run : action.run w=.ok (result,v)) :
    HolderAccount temporary v.wg ∧ Support sessions locals active v.wg := by
  have fields := congrArg (fun s : ProductStore43=>s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp same w result v run)
  exact ⟨keys_store before.1 fields,support_store before.2 fields⟩

theorem local_store {action : Leanux.M α} (same : SameProductStore action)
    (before : LocalKey pkt temporary w.wg ∧ Support sessions locals active w.wg)
    (run : action.run w=.ok (result,v)) :
    LocalKey pkt temporary v.wg ∧ Support sessions locals active v.wg := by
  obtain ⟨allocation,slot,keys⟩ := before.1
  obtain ⟨after,support⟩ := product_store same ⟨keys,before.2⟩ run
  exact ⟨⟨allocation,slot,after⟩,support⟩

theorem lift_keys {P : List RxJoint.Event → World → Prop} (action : Leanux.M α)
    (same : SameProductStore action) (old : PrefixPreserves P (fun _=>True) (liftPrefix action)) :
    PrefixPreserves (WithKeys sessions locals active temporary P) (fun _=>True) (liftPrefix action) := by
  apply extend (Appends.lift _) old
  intro w h result v _ before run
  exact product_store same before (by simpa only [runPrefix_lift] using run)

theorem lift_local {P : List RxJoint.Event → World → Prop} (action : Leanux.M α)
    (same : SameProductStore action) (old : PrefixPreserves P (fun _=>True) (liftPrefix action)) :
    PrefixPreserves (WithLocal sessions locals active pkt temporary P) (fun _=>True) (liftPrefix action) := by
  apply extend (Appends.lift _) old
  intro w h result v _ before run
  exact local_store same before (by simpa only [runPrefix_lift] using run)

theorem receipt_local {P : List RxJoint.Event → World → Prop} (action : Leanux.M α)
    (same : SameProductStore action) (f : RunWitness α→RxJoint.Event)
    (old : PrefixPreserves P (fun _=>True) (receiptObserved (liftPrefix action) f)) :
    PrefixPreserves (WithLocal sessions locals active pkt temporary P) (fun _=>True)
      (receiptObserved (liftPrefix action) f) := by
  apply extend (Appends.lift _).receiptObserved old
  intro w h result v _ before run
  exact local_store same before ((RxLink.receipt_erases (erasesPrefix_lift _) w h).symm.trans run)

theorem cleanup_phase_bind (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer=pid) (tail : Obs α)
    (next : PrefixEnsures (WithKeys sessions locals active temporary (Accounted (StableBoundary initial) loans))
      (fun _=>True) tail Q) :
    PrefixEnsures
      (WithLocal sessions locals active pkt temporary
        (Accounted (fun ls h w=>Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans))
      (fun _=>True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _←liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q := by
  simpa only [bind_assoc] using PrefixEnsures.bind
    (cleanup_phase initial loans pid skb stamp pkt flag guard) (fun u=>by cases u; exact next)

theorem cleanup_live_phase_bind (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer=pid) (tail : Obs α)
    (next : PrefixEnsures (WithKeys sessions locals active temporary (Accounted (StableBoundary initial) loans))
      (fun _=>True) tail Q) :
    PrefixEnsures
      (WithLocal sessions locals active pkt temporary
        (Accounted (fun ls h w=>Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w) loans))
      (fun _=>True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _←liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q :=
  (cleanup_phase_bind initial loans pid skb stamp pkt flag guard tail next).consequence
    (fun _ _ ⟨⟨holders,aligned,live,stable⟩,keys,support⟩=>⟨⟨holders,aligned,live.1,stable⟩,keys,support⟩)
    (fun _ _ _ before=>before)

end Leanux.Proofs.WG.RetirementSecurity.HolderPoll
