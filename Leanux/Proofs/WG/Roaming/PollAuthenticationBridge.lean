import Leanux.Proofs.WG.Roaming.PollAuthenticationEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes RxJoint

def EventFacts (history : List RxHistory.Event) : Event → Prop
  | .checkedEndpoint _ id stamp pkt r =>
      PublicationHistory.Inv history r.before.wg ∧
      RxDisposition.SelectedAt id stamp pkt r.before ∧ pkt.state = .crypted
  | _ => True

def Checks (history : List RxHistory.Event) (h : List Event) : Prop :=
  ∀e∈h, EventFacts history e

def State (history : List RxHistory.Event) (h : List Event) (w : World) : Prop :=
  PublicationHistory.Inv history w.wg ∧ Checks history h

def Selected (history : List RxHistory.Event) (id : SkbId)
    (stamp : PacketStamp) (pkt : RxPacket) (h : List Event) (w : World) : Prop :=
  State history h w ∧ RxDisposition.SelectedAt id stamp pkt w

end Leanux.Proofs.WG.Roaming.PollAuthentication
