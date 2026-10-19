import Leanux.Proofs.WG.RetirementSecurity.HolderPollSupport
import Leanux.Proofs.WG.RetirementSecurity.RxSelectedCredit
import Leanux.Proofs.WG.Queues.HolderPollBoundary

/-! Key-credit extensions of the existing native poll observer's actual
phases. The selected key allocation is transferred at dequeue and remains a
separate temporary credit until the original cleanup pays it. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open RxJoint PollCarrier DurableHolders

def WithKeys (sessions : List SessionOrigin.Receipt) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (temporary : Credits.Ledger)
    (P : List RxJoint.Event → World → Prop) (h : List RxJoint.Event) (w : World) :=
  P h w ∧ HolderAccount temporary w.wg ∧ Support sessions locals active w.wg

def LocalKey (pkt : RxPacket) (temporary : Credits.Ledger) (w : WGWorld) :=
  ∃ allocation, pkt.keypair=allocation.slot ∧ HolderAccount (allocation::temporary) w

def WithLocal (sessions : List SessionOrigin.Receipt) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (pkt : RxPacket) (temporary : Credits.Ledger)
    (P : List RxJoint.Event → World → Prop) (h : List RxJoint.Event) (w : World) :=
  P h w ∧ LocalKey pkt temporary w.wg ∧ Support sessions locals active w.wg

theorem extend {P : List RxJoint.Event → World → Prop}
    {Q : α → List RxJoint.Event → World → Prop} {observer : Obs α}
    {R : World → Prop} {S : α → World → Prop}
    (appends : Appends observer) (old : PrefixEnsures P (fun _=>True) observer Q)
    (extra : ∀ w h result v, P h w → R w →
      (runPrefix observer w h).1=.ok (result,v) → S result v) :
    PrefixEnsures (fun h w=>P h w ∧ R w) (fun _=>True) observer
      (fun result h w=>Q result h w ∧ S result w) := by
  apply normal_spec appends
  intro w h result v before run
  have post := (old w h before.1).choose_spec.2.2
  rw [run] at post
  exact ⟨post,extra w h result v before.1 before.2 run⟩

theorem native_receipt {action : WG.M α} {w v : World}
    (run : (liftWG action).run w=.ok (result,v)) :
    (action.run w.wg).run w.ambient=.ok ((result,v.wg),v.ambient) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    action w v result run

theorem peek_phase (initial : Ledger) (loans : Reservations) (pid : PeerId) :
    PrefixEnsures
      (WithKeys sessions locals active temporary (Accounted (StableBoundary initial) loans))
      (fun _=>True) (access (liftWGObserver (peekAccess pid)))
      (fun first=>WithKeys sessions locals active temporary
        (Accounted (fun ls h w=>AfterPeek initial ls pid first h w ∧
          StableAt initial h w ∧ HeadAt pid first w) loans)) := by
  apply extend (access_appends _) (peek_accounted initial loans pid)
  intro w h result v _ before run
  have native := native_receipt
    ((access_erases (liftWGObserver_erases (peekAccess_erases pid)) w h).symm.trans run)
  exact ⟨(before.1.peek_rx pid w.ambient v.ambient native).1,
    (hoare_iff_run_ambient _ _ _).mp (peek pid) w.wg w.ambient result v.wg v.ambient before.2 native⟩

theorem ready_phase (initial : Ledger) (loans : Reservations) (pid : PeerId) (first : Option SkbId) :
    PrefixEnsures
      (WithKeys sessions locals active temporary
        (Accounted (fun ls h w=>AfterPeek initial ls pid first h w ∧
          StableAt initial h w ∧ HeadAt pid first w) loans))
      (fun _=>True) (access (liftWGObserver (readyAccess first)))
      (fun go=>WithKeys sessions locals active temporary
        (Accounted (fun ls h w=>AfterPeek initial ls pid first h w ∧ StableAt initial h w ∧
          (go=false → ColdHead pid w.wg) ∧ (go=true → ReadyPacket first w)) loans)) := by
  apply extend (access_appends _) (ready_accounted initial loans pid first)
  intro w h result v _ before run
  have native := native_receipt
    ((access_erases (liftWGObserver_erases (readyAccess_erases first)) w h).symm.trans run)
  have same := (ready_result first w.wg v.wg result w.ambient v.ambient native).1
  simpa only [same] using before

theorem capture_phase (initial : Ledger) (loans : Reservations) (pid skb : Nat) :
    PrefixEnsures
      (WithKeys sessions locals active temporary
        (Accounted (fun ls h w=>AfterPeek initial ls pid (some skb) h w ∧
          StableAt initial h w ∧ ReadyPacket (some skb) w) loans))
      (fun _=>True) (capture skb)
      (fun out=>WithKeys sessions locals active temporary
        (Accounted (fun ls h w=>Captured initial ls pid skb out h w ∧
          StableAt initial h w ∧ out.1.state≠.uncrypted) loans)) := by
  apply extend (capture_appends _) (capture_accounted initial loans pid skb)
  intro w h result v _ before run
  rw [(RxDisposition.capture_selected skb w v h result.1 result.2 run).1]
  exact before

theorem drop_erases (pid n skb : Nat) (stamp : PacketStamp) :
    ErasesPrefix (RxJoint.drop pid n skb stamp) (liftWG (dropRxQueue pid)) := by
  unfold RxJoint.drop
  simpa only [bind_pure_unit,dropRxQueue] using erasesPrefix_bind
    (access_erases (liftWGObserver_erases (rxDropPeekedPrefix_erases pid)))
    (fun _=>erasesPrefix_emit _)

theorem drop_phase (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ready : pkt.state≠.uncrypted) :
    PrefixEnsures
      (WithKeys sessions locals active temporary
        (Accounted (fun ls h w=>Captured initial ls pid skb (pkt,stamp) h w ∧ StableAt initial h w) loans))
      (fun _=>True) (RxJoint.drop pid n skb stamp)
      (fun _=>WithLocal sessions locals active pkt temporary
        (Accounted (fun ls h w=>Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w) loans)) := by
  apply extend ((access_appends _).bind (fun _=>emit_appends _))
    (drop_accounted initial loans pid n skb stamp pkt ready)
  intro w h result v old before run
  cases result
  have native := native_receipt ((drop_erases pid n skb stamp w h).symm.trans run)
  obtain ⟨holders,aligned,captured,stable⟩ := old
  obtain ⟨d,p,device,resident,peeked⟩ := captured.1.2
  obtain ⟨allocation,loan,keys⟩ := before.1.drop_rx_native
    (by simp [peerAt,device,resident]) peeked w.ambient v.ambient native
  have packet : d.rxSkbs[skb]?=some pkt := by
    simpa [RxDisposition.SelectedAt,RxDisposition.rxStore,RxDisposition.nativeRxStore,device] using captured.2.2
  have named : nameLoan w.wg (.receive pid skb) pkt.keypair=some ⟨.receive pid skb,allocation⟩ := by
    simpa [receiveLoan,device,packet] using loan
  have slot := (nameLoan_resident named).2.1
  exact ⟨⟨allocation,slot.symm,keys⟩,
    (hoare_iff_run_ambient _ _ _).mp (drop pid) w.wg w.ambient () v.wg v.ambient before.2 native⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderPoll
