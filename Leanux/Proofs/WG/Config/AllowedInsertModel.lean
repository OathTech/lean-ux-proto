import Leanux.WG.NetlinkDump

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

def allowedBits (v4 : Bool) : Nat := if v4 then 32 else 128
def allowedFamily (v4 : Bool) : Nat := if v4 then 4 else 6
def allowedRoot (v4 : Bool) : Slot := if v4 then .root4 else .root6
def allowedRootValue (v4 : Bool) (d : Device) : Option NodeId :=
  if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
def allowedAttrs (v4 : Bool) (addr cidr : Nat) : AllowedIpAttrs :=
  { family := some (if v4 then AF_INET else AF_INET6), addr := some addr,
    addrLen := if v4 then 4 else 16, cidr := some cidr }

def insertSequenceDevice (d : Device) : Device :=
  { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }

/-- Allocation, list append, node-parent write and root write remain ordered.
The allocation cursor may already name a node: its overwrite is retained. -/
def emptyRootInserted (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (addr cidr : Nat) : Device :=
  let id := d.nextNode
  let n := newNode addr cidr (allowedBits v4) (some pid)
  let allocated := { d with nextNode := id + 1, nodes := d.nodes.insert id n }
  let listed := { allocated with peers := allocated.peers.insert pid ({ p with allowedipsList := p.allowedipsList ++ [id] }) }
  let parented := { listed with nodes := listed.nodes.insert id { n with parent := allowedRoot v4 } }
  { parented with peerAllowedips := if v4 then
      { parented.peerAllowedips with root4 := some id }
    else { parented.peerAllowedips with root6 := some id } }

def EmptyRootInsertEffect (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (addr cidr : Nat) (ret : Int) (final : Device) : Prop :=
  (ret = -ENOMEM ∧ final = insertSequenceDevice d) ∨
  (ret = 0 ∧ final = emptyRootInserted v4 (insertSequenceDevice d) pid p addr cidr)

/-- The mirror's exact masking formula. Fixed-width hex serialization below
also truncates any bits above the selected address width. -/
def allowedMasked (v4 : Bool) (addr cidr : Nat) : Nat :=
  if cidr = 0 then 0 else addr / 2 ^ (allowedBits v4 - cidr) * 2 ^ (allowedBits v4 - cidr)

def allowedJson (v4 : Bool) (addr cidr : Nat) : Json :=
  Json.mkObj [("family", toJson (allowedFamily v4)),
    ("addr", toJson (hexBE (allowedMasked v4 addr cidr) (if v4 then 4 else 16))),
    ("cidr", toJson cidr)]

end Leanux.Proofs.WG.Config
