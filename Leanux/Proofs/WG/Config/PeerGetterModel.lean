import Leanux.Proofs.WG.Config.PeerPageStartModel
import Leanux.Proofs.WG.Config.PeerPageTailModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Canonical complete-peer DATA pages in original occurrence order, with device
attributes only on the first and successful DONE at the end. -/
def peerGetterMessages (d : Device) (peers : PeerId → Peer) : List NlMessage :=
  let first := peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList
  .data 2 (deviceFixedAttrs d)
    (if d.peerList.isEmpty then none else some (multiPeerParts peers first.1)) ::
      (peerTailPages peers (NLMSG_GOODSIZE-24) first.2).map
        (fun page => .data 2 [] (some (multiPeerParts peers page))) ++ [.done 2 0]

/-- Exact ordered Device updates prescribed by canonical nonfinal cursor
handoffs. A completing first page performs no reference update. -/
def peerGetterFinalDevice (d : Device) (peers : PeerId → Peer) : Device :=
  let first := peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList
  if first.2.isEmpty then d else
    peerPagesDevice (peerFirstDevice d peers) first.1.getLast?
      (peerTailPages peers (NLMSG_GOODSIZE-24) first.2)


end Leanux.Proofs.WG.Config
