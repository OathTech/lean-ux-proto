import Leanux.WG.NetlinkDump

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Exact serialized bytes selected by the node's actual family branch. -/
def dumpNodeSpace (n : AipNode) : Nat := if n.bitlen = 32 then 28 else 40

/-- Exact read_node mask and get_allowedips JSON, including arbitrary stored
widths. A non-32 width selects family 6 but still masks using that stored width;
this definition does not assert that the node is a valid IPv6 node. -/
def dumpNodeJson (n : AipNode) : Json :=
  let masked := if n.cidr = 0 then 0 else n.bits / 2 ^ (n.bitlen - n.cidr) * 2 ^ (n.bitlen - n.cidr)
  Json.mkObj [("family",toJson (if n.bitlen = 32 then (4 : Nat) else 6)),
    ("addr",toJson (hexBE masked (if n.bitlen = 32 then 4 else 16))), ("cidr",toJson n.cidr)]

def dumpNodeJsons (nodes : NodeId → AipNode) (ids : List NodeId) : Array Json :=
  (ids.map fun id => dumpNodeJson (nodes id)).toArray

def dumpNodesSpace (nodes : NodeId → AipNode) (ids : List NodeId) : Nat :=
  (ids.map fun id => dumpNodeSpace (nodes id)).sum

end Leanux.Proofs.WG.Config
