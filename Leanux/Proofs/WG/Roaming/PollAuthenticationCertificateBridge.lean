import Leanux.Proofs.WG.Roaming.PollAuthenticationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes PublicationIdentity
open Origins.HistorySupport (sessions)

def Certified (history : List RxHistory.Event) (id : SkbId) (stamp : PacketStamp)
    (pkt : RxPacket) (receipt : RunWitness (Option Endpoint)) : Prop :=
  receipt.Valid (liftWG (endpointFromSkb pkt.source)) ∧
  receipt.value = some (sourceEndpoint pkt.source) ∧
  (pkt.source.family = 4 ∨ pkt.source.family = 6) ∧
  ∃ prior later, ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)),
    ∃ out published ambient,
    history = prior ++ .rx (.decrypt id decrypt) :: later ∧
    Published id decrypt out pkt.peer published ambient ∧
    Retained (sessions prior) id decrypt out pkt.peer published receipt.before.wg ∧
    pkt = {out with state := .crypted} ∧ stamp = packetStamp published id

def Safe (h : List RxHistory.Event) : Prop :=
  ∀ pre n id stamp pkt r post,
    h = pre ++ .checkedEndpoint n id stamp pkt r :: post →
    Certified pre id stamp pkt r

def Reached (h : List RxHistory.Event) (w : World) : Prop :=
  PublicationJoint.Inv h w ∧ Safe h

end Leanux.Proofs.WG.Roaming.PollAuthentication
