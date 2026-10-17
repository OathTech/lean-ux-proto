import Leanux.Proofs.WG.Config.DumpCoalesce
import Leanux.Proofs.WG.Config.AllowedInsertModel

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

def multipartFirst (p : Peer) (addr cidr : Nat) : PeerDumpAttrs :=
  { publicKey := hexKey p.remoteStatic
    attrs := peerFixedAttrs p ++ [("allowed_ips", Json.arr #[allowedJson true addr cidr])]
    split := true }

def multipartLast (p : Peer) (addr cidr : Nat) : PeerDumpAttrs :=
  { publicKey := hexKey p.remoteStatic
    attrs := [("public_key", toJson (hexKey p.remoteStatic)),
      ("allowed_ips", Json.arr #[allowedJson true addr cidr])] }

def multipartJson (d : Device) (p : Peer) (addr₁ cidr₁ addr₂ cidr₂ : Nat) : Json :=
  Json.mkObj (deviceFixedAttrs d ++ [("peers", Json.arr #[Json.mkObj
    (peerFixedAttrs p ++ [("allowed_ips", Json.arr
      #[allowedJson true addr₁ cidr₁, allowedJson true addr₂ cidr₂])])])])

abbrev PeerDumpResult := NlSkb × DumpCtx × PeerDump

/-- Two original getter calls share their actual returned context. Coalescing
uses their actual fragments; unexpected fragment kinds stop explicitly. Chunk
capacities are supplied by this composition, not by the socket dump scheduler. -/
def multipartPeerDump (pid : PeerId) (d : Device) (ctx : DumpCtx)
    (firstSkb secondSkb : NlSkb) : WG.M (PeerDumpResult × PeerDumpResult × Except Int Json) := do
  let first ← getPeerDump pid ctx firstSkb
  let second ← getPeerDump pid first.2.1 secondSkb
  let (.split firstPeer, .complete secondPeer) := (first.2.2, second.2.2)
    | invariant "multipart proof composition: expected split followed by completion"
  let merged ← coalesce [.data 2 (deviceFixedAttrs d) (some [firstPeer]),
    .data 2 [] (some [secondPeer]), .done 2 0]
  return (first, second, merged)

end Leanux.Proofs.WG.Config
