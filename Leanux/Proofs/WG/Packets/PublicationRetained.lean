import Leanux.Proofs.WG.Packets.PublicationConsume

/-! Transport of a published packet permits peer absence between calls. A normal
consume call itself proves the peer is resident at its entry. The historical
certificate is fixed throughout; later receiving-key validity is irrelevant. -/
namespace Leanux.Proofs.WG.PublicationIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Std.Do MaterialOrigin
variable {id : SkbId}

/-- A peer that still resides at this raw slot has the published identity.
Absence is permitted, and no receiving-key validity is asserted. -/
def PeerSurvives (pid : PeerId) (published current : WGWorld) : Prop :=
  ∀ d p, current.dev = some d → d.peers[pid]? = some p →
    (CurrentIdentity.peerView published).bind (fun peers => peers pid) =
      some (CurrentIdentity.identity p)

def Retained (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (published current : WGWorld) : Prop :=
  CurrentCertificate history id r out pid published ∧
  packetStamp current id = packetStamp published id ∧
  (RxDisposition.nativeRxStore current).2 id = some {out with state := .crypted} ∧
  PeerSurvives pid published current

theorem Live.retained (h : Live history id r out pid published w) :
    Retained history id r out pid published w := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro d p hd hp
  rw [← h.2.2.2]
  simp only [CurrentIdentity.peerView,hd,Option.map_some,Option.bind_some,hp]

theorem Retained.live (h : Retained history id r out pid published w)
    (resident : ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p) :
    Live history id r out pid published w := by
  obtain ⟨d,p,hd,hp⟩ := resident
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  rw [h.2.2.2 d p hd hp]
  simp only [CurrentIdentity.peerView,hd,Option.map_some,Option.bind_some,hp]

/-- The selected packet remains exact, while surviving peer cells are related
pointwise. Unrelated cells may change and the selected peer may disappear. -/
theorem Retained.transport (h : Retained history id r out pid published w)
    (stamp : packetStamp v id = packetStamp w id)
    (packet : (RxDisposition.nativeRxStore v).2 id = (RxDisposition.nativeRxStore w).2 id)
    (peers : ∀ d p, v.dev = some d → d.peers[pid]? = some p →
      ∃ old q, w.dev = some old ∧ old.peers[pid]? = some q ∧
        CurrentIdentity.identity p = CurrentIdentity.identity q) :
    Retained history id r out pid published v := by
  refine ⟨h.1,stamp.trans h.2.1,packet.trans h.2.2.1,?_⟩
  intro d p hd hp
  obtain ⟨old,q,ho,hq,same⟩ := peers d p hd hp
  exact (h.2.2.2 old q ho hq).trans (congrArg some same.symm)

/-- Normal endpoint update starts by reading this peer, before any state write. -/
theorem endpoint_peer_resident (pid : PeerId) (ep : Endpoint)
    (w v : WGWorld) (a b : Ambient)
    (hr : ((setPeerEndpoint pid ep).run w).run a = .ok (((),v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p := by
  unfold setPeerEndpoint at hr
  simp only [requireNotPending,pure_bind] at hr
  rw [bind_ok_ambient] at hr
  obtain ⟨p,u,middle,hread,_⟩ := hr
  obtain ⟨_,_,d,hd,hp⟩ := Origins.getPeer_return pid w u p a middle hread
  exact ⟨d,p,hd,hp⟩

/-- A normal consume, including normal nondelivery, establishes residency at its
actual entry. Cleanup may remove that peer later in the same execution. -/
theorem consume_peer_resident (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (w v : WGWorld) (a b : Ambient) (result : Option (List UInt8))
    (hr : ((consumeDataDone pid pkt ep).run w).run a = .ok ((result,v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p := by
  unfold consumeDataDone at hr
  rw [bind_ok_ambient] at hr
  obtain ⟨value,u,middle,he,_⟩ := hr
  cases value
  exact endpoint_peer_resident pid ep w u a middle he

/-- A valid source-linked receipt recovers full entry identity from conditional
transport, without a premise keeping the peer resident through earlier work. -/
theorem retained_receipt
    (retained : Retained history id r out pid published receipt.run.before)
    (source : RxLink.Source id stamp receipt) :
    ConsumeCertificate history id r out pid published stamp receipt := by
  have packet : receipt.packet = {out with state := .crypted} :=
    Option.some.inj (source.2.1.2.symm.trans retained.2.2.1)
  have owner : out.peer = pid := retained.1.live.packet_peer
  have same : receipt.peer = pid := by
    have hp := source.2.2
    rw [packet] at hp
    exact hp.symm.trans owner
  have resident := consume_peer_resident receipt.peer receipt.packet receipt.endpoint
    receipt.run.before receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter
    receipt.run.value source.1
  rw [same] at resident
  exact live_receipt (retained.live resident) source

end Leanux.Proofs.WG.PublicationIdentity
