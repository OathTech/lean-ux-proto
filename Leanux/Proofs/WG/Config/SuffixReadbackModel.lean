import Leanux.Proofs.WG.Config.MultipartModel

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Only the node fields read by the original serializer are constrained.
Ownership, trie shape, address bounds and global list uniqueness are not needed. -/
def Ipv4Residents (d : Device) (nodes : NodeId → AipNode) (ids : List NodeId) : Prop :=
  ∀ id ∈ ids, d.nodes[id]? = some (nodes id) ∧ (nodes id).bitlen = 32

def ipv4NodeJson (n : AipNode) : Json := allowedJson true n.bits n.cidr

def ipv4Jsons (nodes : NodeId → AipNode) (ids : List NodeId) : Array Json :=
  (ids.map fun id => ipv4NodeJson (nodes id)).toArray

def suffixLast (p : Peer) (nodes : NodeId → AipNode) (ids : List NodeId) : PeerDumpAttrs :=
  { publicKey := hexKey p.remoteStatic
    attrs := [("public_key", toJson (hexKey p.remoteStatic)),
      ("allowed_ips", Json.arr (ipv4Jsons nodes ids))] }

def suffixJson (d : Device) (p : Peer) (nodes : NodeId → AipNode) (ids : List NodeId) : Json :=
  Json.mkObj (deviceFixedAttrs d ++ [("peers", Json.arr #[Json.mkObj
    (peerFixedAttrs p ++ [("allowed_ips", Json.arr (ipv4Jsons nodes ids))])])])

end Leanux.Proofs.WG.Config
