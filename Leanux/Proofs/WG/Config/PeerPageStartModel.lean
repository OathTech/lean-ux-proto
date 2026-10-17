import Leanux.Proofs.WG.Config.PeerPagePlanModel
import Leanux.Proofs.WG.Config.CursorCallbackModel
import Leanux.Proofs.WG.Config.PaginationBoundaryModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The first maximal DATA page and its actual completion/cursor metadata. -/
def peerFirstCall (d : Device) (peers : PeerId → Peer) : DumpCall :=
  let result := peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList
  let room := NLMSG_GOODSIZE-devicePrefixSpace d-multiPeerSpace peers result.1
  {ret := if result.2.isEmpty then 0 else Int.ofNat (NLMSG_GOODSIZE-room),
   skb := {room,messages := [.data 2 (deviceFixedAttrs d)
     (if d.peerList.isEmpty then none else some (multiPeerParts peers result.1))]},
   ctx := {hasWg := true,nextPeer := if result.2.isEmpty then none else result.1.getLast?},
   prevSeq := d.deviceUpdateGen}

/-- Only a nonfinal first page acquires a cursor reference. -/
def peerFirstDevice (d : Device) (peers : PeerId → Peer) : Device :=
  let result := peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList
  cursorAcquired d (if result.2.isEmpty then none else result.1.getLast?)

/-- Actual idle-start socket result. Completing DATA retains the real DONE-room
branch; a nonfinal page keeps the callback running and queues only DATA. -/
def peerFirstSocket (d : Device) (peers : PeerId → Peer) (sock : NlSock) : NlSock :=
  let call := peerFirstCall d peers
  if call.ret = 0 then
    let started := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
    let complete := paginationCompletedSocket started call
    {complete with queue := sock.queue ++ complete.queue}
  else
    {sock with cbRunning := true,ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := call.ret,queue := sock.queue ++ [call.skb]}


end Leanux.Proofs.WG.Config
