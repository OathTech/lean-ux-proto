import Leanux.Proofs.WG.AuthenticatedEffects.TransportSelection

/-! Original pre-consume replay receipts joined to an earlier authenticated
publication, before the first endpoint/consumer effect and before any later Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportAuthenticatedEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
variable {id : SkbId}

/-- Same historical decrypt, immutable publication and retained live cell at
the replay-check input. The source history must be established at poll entry. -/
def Certified (history : List RxHistory.Event) (id : SkbId) (stamp : PacketStamp)
    (pkt : RxPacket) (r : RunWitness Bool) : Prop :=
  RxDisposition.SelectedAt id stamp pkt r.before ∧ pkt.state = .crypted ∧
  r.Valid (liftWG (counterValidate pkt.keypair pkt.nonce)) ∧
  PublicationHistory.Anchored history id r.before.wg

theorem poll (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent)
    (history : List RxHistory.Event) (hi : PublicationHistory.Inv history w.wg)
    (occurrence id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (r : RunWitness Bool)
    (member : RxJoint.Event.checkedCounter occurrence id stamp pkt r ∈
      (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed prior)).2) :
    Certified history id stamp pkt r := by
  have selected := TransportSelection.poll_selected pid budget w prior occurrence id stamp pkt r member
  obtain ⟨entry,crypted,valid⟩ :=
    TransportEntryChecks.poll_counter_entry pid budget w prior history hi occurrence id stamp pkt r member
  exact ⟨selected,crypted,valid,entry id pkt selected.2 crypted⟩

/-- Every new persistent replay receipt has the same anchored publication,
even when an internally stopped consumer prevents a completed-consume receipt. -/
theorem observePoll (pid : PeerId) (budget : Nat) (w : World)
    (history : List RxHistory.Event) (hi : PublicationHistory.Inv history w.wg) :
    ∃ suffix : List RxJoint.Event,
      runPrefix (RxHistory.observePoll pid budget) w history =
        ((runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior history))).1,
          history ++ suffix.map RxHistory.promote) ∧
      ∀ occurrence id stamp pkt r, RxJoint.Event.checkedCounter occurrence id stamp pkt r ∈ suffix →
        Certified history id stamp pkt r := by
  obtain ⟨suffix,hs⟩ := RxJoint.poll_appends pid budget w (RxJoint.seed (RxHistory.prior history))
  refine ⟨suffix,RxHistory.observePoll_suffix pid budget w history _ suffix (Prod.ext rfl hs),?_⟩
  intro occurrence id stamp pkt r member
  apply poll pid budget w (RxHistory.prior history) history hi occurrence id stamp pkt r
  rw [hs]
  exact List.mem_append_right _ member

/-- Eliminate the anchor to its actual successful native AEAD call and exact
checked plaintext, nonce and key slot; no completed consumer is used. -/
theorem Certified.authenticated (certified : Certified history id stamp pkt r) :
    ∃ pre post, ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      history = pre ++ .rx (.decrypt id decrypt) :: post ∧
      PublicationIdentity.Published id decrypt out pid published ambient ∧
      pkt = {out with state := .crypted} ∧
      ∃ d k, decrypt.before.dev = some d ∧ d.rxSkbs[id]? = some decrypt.value.1 ∧
        d.keypairs[decrypt.value.1.keypair]? = some k ∧ k.receiving.isValid = true ∧
        pkt.keypair = decrypt.value.1.keypair ∧ pkt.nonce = u64le decrypt.value.1.bytes 8 ∧
        aeadDecrypt k.receiving.key (counterNonce pkt.nonce)
          (decrypt.value.1.bytes.drop 16) [] = some pkt.bytes := by
  obtain ⟨selected,_,_,pre,post,decrypt,out,pid,published,ambient,position,publication,retained⟩ := certified
  have packet : pkt = {out with state := .crypted} :=
    Option.some.inj (selected.2.symm.trans retained.2.2.1)
  obtain ⟨d,k,hd,hp,hk,hvalid,_,record,aead⟩ :=
    RxOrigin.decrypt_receipt id decrypt out publication.1 publication.2.1
  have key : out.keypair = decrypt.value.1.keypair := by
    have projected := congrArg RxPacket.keypair record
    exact projected
  have nonce : out.nonce = u64le decrypt.value.1.bytes 8 := by
    have projected := congrArg RxPacket.nonce record
    exact projected
  have packetKey : pkt.keypair = out.keypair := by
    have projected := congrArg RxPacket.keypair packet
    exact projected
  have packetNonce : pkt.nonce = out.nonce := by
    have projected := congrArg RxPacket.nonce packet
    exact projected
  have bytes : pkt.bytes = out.bytes := by
    have projected := congrArg RxPacket.bytes packet
    exact projected
  refine ⟨pre,post,decrypt,out,pid,published,ambient,position,publication,packet,d,k,hd,hp,hk,hvalid,
    packetKey.trans key,packetNonce.trans nonce,?_⟩
  simpa only [packetNonce,nonce,bytes] using aead

end Leanux.Proofs.WG.AuthenticatedEffects.TransportAuthenticatedEntry
