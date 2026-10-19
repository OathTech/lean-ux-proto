import Leanux.Proofs.WG.Config.MixedPageTransportModel
import Leanux.Proofs.WG.Config.MixedPageSelectionModel
import Leanux.Proofs.WG.Config.PaginationBoundaryModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

def mixedFirstScan (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode) : MixedPeerScan :=
  mixedPeerScan d peers nodes (mixedInitialRows d peers) {hasWg := true} none
    {room := mixedPageRoom d {hasWg := true}} #[]

/-- The first native callback restores the peer-nest reservation exactly when
its empty-Device guard cancels it. The underlying scan remains post-nest. -/
def mixedPeersFirstCall (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode) : DumpCall :=
  let call := mixedPageCall d (mixedFirstScan d peers nodes)
  {call with skb := {call.skb with
    room := call.skb.room + if d.peerList.isEmpty then 4 else 0}}

def mixedFirstDevice (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode) : Device :=
  let page := mixedFirstScan d peers nodes
  cursorAcquired d (if page.native.2.2.2.1 then none else page.native.2.1)

def mixedFirstSocket (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (sock : NlSock) : NlSock :=
  let call := mixedPeersFirstCall d peers nodes
  if call.ret = 0 then
    let started := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
    let complete := paginationCompletedSocket started call
    {complete with queue := sock.queue ++ complete.queue}
  else
    {sock with cbRunning := true,ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := call.ret, queue := sock.queue ++ [call.skb]}

end Leanux.Proofs.WG.Config
