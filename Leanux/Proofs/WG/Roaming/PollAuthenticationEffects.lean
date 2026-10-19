import Leanux.Proofs.WG.Packets.PublicationPollChecks
import Leanux.Proofs.WG.Packets.PublicationWorkers
import Leanux.Proofs.WG.Roaming.EndpointClaims
import Leanux.Proofs.WG.Noise.CounterConsumeSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes PublicationIdentity
open Origins.HistorySupport (sessions)

theorem selected_anchored
    {history : List RxHistory.Event} {w : World}
    {id : SkbId} {stamp : PacketStamp} {pkt : RxPacket}
    (packets : PublicationHistory.Inv history w.wg)
    (selected : RxDisposition.SelectedAt id stamp pkt w)
    (crypted : pkt.state = .crypted) :
    ∃ prior later, ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)),
      ∃ out published ambient,
      history = prior ++ .rx (.decrypt id decrypt) :: later ∧
      Published id decrypt out pkt.peer published ambient ∧
      Retained (sessions prior) id decrypt out pkt.peer published w.wg ∧
      pkt = {out with state := .crypted} ∧
      stamp = packetStamp published id := by
  obtain ⟨prior,later,decrypt,out,pid,published,ambient,position,publication,retained⟩ :=
    packets id pkt selected.2 crypted
  have packet : pkt = {out with state := .crypted} :=
    Option.some.inj (selected.2.symm.trans retained.2.2.1)
  have owner : pkt.peer = pid := by
    rw [packet]
    exact retained.1.live.packet_peer
  subst pid
  exact ⟨prior,later,decrypt,out,published,ambient,position,publication,retained,
    packet,selected.1.symm.trans retained.2.1⟩

/-- A later successful endpoint prefix suffices for caller identity; no
completion of consumeDataDone is needed. -/
theorem selected_setter_identity
    {history : List RxHistory.Event} {w v : World}
    {id : SkbId} {stamp : PacketStamp} {pkt : RxPacket}
    {ep : Endpoint}
    (packets : PublicationHistory.Inv history w.wg)
    (selected : RxDisposition.SelectedAt id stamp pkt w)
    (crypted : pkt.state = .crypted)
    (setter : ((setPeerEndpoint pkt.peer ep).run w.wg).run w.ambient =
      .ok (((),v.wg),v.ambient)) :
    ∃ prior later, ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)),
      ∃ out published ambient,
      history = prior ++ .rx (.decrypt id decrypt) :: later ∧
      Published id decrypt out pkt.peer published ambient ∧
      Live (sessions prior) id decrypt out pkt.peer published w.wg ∧
      pkt = {out with state := .crypted} ∧
      stamp = packetStamp published id := by
  obtain ⟨prior,later,decrypt,out,published,ambient,position,publication,retained,
    packet,stampEq⟩ := selected_anchored packets selected crypted
  exact ⟨prior,later,decrypt,out,published,ambient,position,publication,
    retained.live (endpoint_peer_resident _ _ _ _ _ _ setter),packet,stampEq⟩

end Leanux.Proofs.WG.Roaming.PollAuthentication
