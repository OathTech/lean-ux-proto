import Leanux.Proofs.WG.RetirementSecurity.HolderPollPhases

/-! The actual replay/confirmation and cleanup source phases retain and pay
the selected RX key credit. Independent stamped peer funding proves that
cleanup cannot erase an allocation still owned by a published peer slot. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open RxJoint PollCarrier DurableHolders

theorem counter_phase (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves
      (WithLocal sessions locals active pkt temporary
        (Accounted (fun ls h w=>Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w) loans))
      (fun _=>True)
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (RxJoint.Event.checkedCounter n skb stamp pkt)) := by
  apply extend (access_appends _).receiptObserved (counter_accounted initial loans pid n skb stamp pkt)
  intro w h result v _ before run
  have native := native_receipt
    ((RxLink.receipt_erases (access_erases (liftWGObserver_erases
      (counterValidatePrefix_erases _ _))) w h).symm.trans run)
  obtain ⟨allocation,slot,keys⟩ := before.1
  exact ⟨⟨allocation,slot,(hoare_iff_run_ambient _ _ _).mp (HolderReplay.counter _ _)
      w.wg w.ambient result v.wg v.ambient keys native⟩,
    (hoare_iff_run_ambient _ _ _).mp (counter _ _) w.wg w.ambient result v.wg v.ambient before.2 native⟩

theorem consume_native (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint)
    (run : (runPrefix (RxJoint.consume pid n skb stamp pkt ep) w h).1=.ok (result,v)) :
    ∃ out, ((consumeDataDone pid pkt ep).run w.wg).run w.ambient=.ok ((out,v.wg),v.ambient) := by
  rw [consume_run] at run
  cases observed : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk answer history => cases answer with
    | error e => simp [observed] at run
    | ok answer =>
      obtain ⟨out,u⟩ := answer
      have native := native_receipt
        ((access_erases (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h).symm.trans
          (congrArg Prod.fst observed))
      cases out <;> simp only [observed,Except.ok.injEq,Prod.mk.injEq] at run
      all_goals obtain ⟨_,same⟩ := run; subst u; exact ⟨_,native⟩

theorem consume_phase (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) (guard : pkt.peer=pid) :
    PrefixEnsures
      (WithLocal sessions locals active pkt temporary
        (Accounted (fun ls h w=>Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w) loans))
      (fun _=>True) (RxJoint.consume pid n skb stamp pkt ep)
      (fun _=>WithLocal sessions locals active pkt temporary
        (Accounted (fun ls h w=>Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans)) := by
  apply extend (consume_appends _ _ _ _ _ _) (consume_accounted initial loans pid n skb stamp pkt ep guard)
  intro w h result v old before run
  obtain ⟨holders,aligned,live,stable⟩ := old
  obtain ⟨o,owner,stampEq,carriers⟩ := live.1
  have packet : packetAt w.wg (packetOfStamp stamp)=some pkt := by
    obtain ⟨epoch,resident⟩ := live.2
    unfold packetAt packetOfStamp Lifetimes.packetStamp at *
    cases device:w.wg.dev with
    | none => simp [RxDisposition.rxStore,RxDisposition.nativeRxStore,device] at resident
    | some d => simpa [RxDisposition.rxStore,RxDisposition.nativeRxStore,device,←epoch] using resident
  have compatible : KeyCompatible pid pkt.keypair w.wg := guard ▸ carriers.packet_key (c:=Selected stamp o) packet
  obtain ⟨out,native⟩ := consume_native pid n skb stamp pkt ep run
  obtain ⟨allocation,slot,keys⟩ := before.1
  exact ⟨⟨allocation,slot,keys.receive_done before.2.1.1.bounded compatible ep w.ambient v.ambient native⟩,
    (hoare_iff_run_ambient _ _ _).mp (consume pid pkt ep) w.wg w.ambient out v.wg v.ambient before.2 native⟩

theorem cleanup_erases (pid skb : Nat) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer=pid) :
    ErasesPrefix
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _←liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb)))
      (liftWG (RxCredits.cleanup skb pkt flag)) := by
  rw [cleanup_poll_guard skb pkt pid flag guard]
  simp only [liftWG_bind]
  exact erasesPrefix_bind (access_erases (liftWGObserver_erases (keypairPutPrefix_erases _ _))) (fun _=>
    erasesPrefix_bind (access_erases (liftWGObserver_erases (peerPutMixed_erases _))) (fun _=>
    erasesPrefix_bind (erasesPrefix_lift _) (fun _=>access_erases (liftWGObserver_erases (freeRxSkbPrefix_erases _)))))

theorem cleanup_phase (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer=pid) :
    PrefixEnsures
      (WithLocal sessions locals active pkt temporary
        (Accounted (fun ls h w=>Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans))
      (fun _=>True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _←liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb)))
      (fun _=>WithKeys sessions locals active temporary (Accounted (StableBoundary initial) loans)) := by
  apply extend ((access_appends _).bind (fun _=>(access_appends _).bind (fun _=>
    (Appends.lift _).bind (fun _=>access_appends _))))
    (cleanup_accounted initial loans pid skb stamp pkt flag guard)
  intro w h result v old before run
  cases result
  obtain ⟨holders,aligned,⟨o,owner,stampEq,carriers⟩,stable⟩ := old
  have funded : holders.Funded (Selected stamp o::rest initial h) loans w.wg := ⟨aligned,carriers⟩
  obtain ⟨p,resident,_⟩ := selected_credit funded.carriers.funded rfl
  obtain ⟨d,device,epoch,_,_⟩ := resident_fields resident
  have present := funded.carriers.inventory.present (Selected stamp o) (by simp)
  have packet : (Selected stamp o).packet=⟨d.ifindex,skb⟩ := by
    have sameEpoch : stamp.1=d.ifindex := present.1.trans epoch.symm
    simp only [Selected,packetOfStamp,sameEpoch,stampEq,Nat.add_sub_cancel]
  have native := native_receipt ((cleanup_erases pid skb pkt flag guard w h).symm.trans run)
  obtain ⟨allocation,slot,keys⟩ := before.1
  exact ⟨(keys.cleanup_rx_selected funded (anchors before.2 funded) rfl device packet
      (guard.trans owner.symm) slot flag w.ambient v.ambient native).1,
    (hoare_iff_run_ambient _ _ _).mp (cleanup skb pkt flag) w.wg w.ambient () v.wg v.ambient before.2 native⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderPoll
