import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.Proofs.WG.Campaign2.Bridge
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- The complete original buffer sender with its allocation loop replaced by
the existing finite encounter evaluator. Routing and transmission retain their
original captured bounds and finite traversals. -/
def sendBuffer (pid : PeerId) (bytes : List UInt8) : WG.M Unit := do
  -- `alloc_skb(len + SKB_HEADER_LEN, GFP_ATOMIC)` (socket.c:192); NULL: -ENOMEM,
  -- which every caller ignores (send.c:40,103)
  if ← branch .sendBufNoMem !(← monadLift (hiddenAllocFinite .sendBufSkb)) then return
  let p ← getPeer pid
  let family := (p.endpoint.map (·.family)).getD 0
  -- W9: send4/send6 are mirrored (Socket.lean), with the peer's endpoint
  -- cache; the IP ident cut and the loopback NET_RX section are at their
  -- transmit
  let e := p.endpoint.getD { family := 0, addr := 0, port := 0 }
  let ret ← do
    -- the DS field of every handshake message is HANDSHAKE_DSCP (send.c:41, :105; W5, 2.6)
    if ← branch .sendSkbInet (family == AF_INET) then send4 e (some pid) bytes HANDSHAKE_DSCP true
    else if ← branch .sendSkbInet6 (family == AF_INET6) then send6 e (some pid) bytes HANDSHAKE_DSCP true
    else pure (-EAFNOSUPPORT)   -- dev_kfree_skb
  if ← branch .sendSkbOk (ret == 0) then
    let p ← getPeer pid
    setPeer pid { p with txBytes := p.txBytes + bytes.length }

theorem sendBuffer_source (pid : PeerId) (bytes : List UInt8) :
    WG.sendBufferToPeer pid bytes = sendBuffer pid bytes := by
  unfold WG.sendBufferToPeer sendBuffer
  have allocation : (hiddenAlloc .sendBufSkb : WG.M Bool) =
      monadLift (hiddenAllocFinite .sendBufSkb) := by
    change monadLift (AmbientM.hiddenAlloc .sendBufSkb) = _
    rw [hiddenAlloc_finite_source]
  rw [allocation]

end Leanux.Proofs.WG.Progress.HandshakeFinite
