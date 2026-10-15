import Leanux.Proofs.WG.Config.SuffixReadbackClaims
import Leanux.Proofs.WG.Config.Getter

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

def socketFirstPeer (p : Peer) (nodes : NodeId → AipNode) (front : List NodeId) : PeerDumpAttrs :=
  { publicKey := hexKey p.remoteStatic
    attrs := peerFixedAttrs p ++ [("allowed_ips", Json.arr (ipv4Jsons nodes front))]
    split := true }

def socketFirstCall (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) : DumpCall :=
  let room := NLMSG_GOODSIZE - (devicePrefixSpace d + 140 + 28 * front.length)
  { ret := Int.ofNat (NLMSG_GOODSIZE - room)
    skb := { room, messages := [.data 2 (deviceFixedAttrs d) (some [socketFirstPeer p nodes front])] }
    ctx := { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
    prevSeq := d.deviceUpdateGen }

def socketLastCall (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) : DumpCall :=
  { ret := 0
    skb := { room := NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + 28 * ids.length)
             messages := [.data 2 (deviceFixedAttrs d) (some [suffixLast p nodes ids])] }
    ctx := { hasWg := true }
    prevSeq := d.deviceUpdateGen }

def socketLastChunk (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) : NlSkb :=
  let skb := (socketLastCall d p nodes ids).skb
  { skb with room := skb.room - 20, messages := skb.messages ++ [.done 2 0] }

def socketFirstState (old : NlSock) (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) : NlSock :=
  let call := socketFirstCall d p nodes front b
  { old with
    queue := old.queue ++ [call.skb], ctx := call.ctx
    prevSeq := call.prevSeq, dumpDoneErrno := call.ret, cbRunning := true }

def socketLastState (old : NlSock) (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) : NlSock :=
  { old with
    queue := old.queue ++ [socketLastChunk d p nodes ids]
    ctx := { hasWg := true }, prevSeq := d.deviceUpdateGen, dumpDoneErrno := 0, cbRunning := false }

def socketReadbackFinal (old : NlSock) (d : Device) : NlSock :=
  { old with
    queue := [], ctx := { hasWg := true }
    prevSeq := d.deviceUpdateGen, dumpDoneErrno := 0, cbRunning := false }

/-- The single-peer callback's exact result. The socket decides whether DONE
fits later; this value contains only the original DATA message. -/
def socketCallbackResult (d : Device) (ctx : DumpCtx) (room : Nat)
    (peer : PeerDumpAttrs) (more : Bool) : DumpCall :=
  { ret := if more then Int.ofNat (NLMSG_GOODSIZE - room) else 0
    skb := { room, messages := [.data 2 (deviceFixedAttrs d) (some [peer])] }
    ctx := { ctx with nextPeer := none }
    prevSeq := d.deviceUpdateGen }

end Leanux.Proofs.WG.Config
