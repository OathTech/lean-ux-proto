import PairMemory
import AllowedipsFixture
import AllowedipsLayout

namespace Binary.Pair.Trie
open Leanux Leanux.WG

structure Names where
  nodes : List (NodeId × Nat)
  peers : List (PeerId × Nat)
  deriving Repr

def pointer (names : List (Nat × Nat)) (path : String) (a : Nat) : Decode (Option Nat) :=
  if a == 0 then .ok none
  else match names.find? (·.2 == a) with
    | some (id, _) => .ok (some id)
    | none => .error ⟨path, a, "unresolved pointer"⟩

structure Node where
  peer : Option PeerId
  children : Array (Option NodeId)
  cidr : Nat
  width : Nat
  key : Nat
  deriving Repr, BEq

def targetNode (n : AipNode) : Node := ⟨n.peer, n.bit, n.cidr, n.bitlen, n.bits⟩

structure State where
  nodes : List (NodeId × Node)
  counts : List (PeerId × Nat)
  deriving Repr, BEq

def target (d : Device) : State :=
  ⟨d.nodes.toList.map (fun (id, n) => (id, targetNode n)),
    d.peers.toList.map (fun (id, p) => (id, p.refcount))⟩

def decodeNode (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem) (a : Nat) : Decode Node := do
  let peer ← pointer names.peers "node.peer" (← word m "node.peer" (a+o.peer) 8)
  let mut children := #[]
  for bit in [:2] do
    children := children.push (← pointer names.nodes s!"node.child[{bit}]"
      (← word m s!"node.child[{bit}]" (a+o.children+8*bit) 8))
  let cidr ← word m "node.cidr" (a+o.cidr) 1
  let width ← word m "node.width" (a+o.bitlen) 1
  unless (width == 32 || width == 128) && cidr ≤ width do
    throw ⟨"node.prefix", a, s!"invalid family/prefix {width}/{cidr}"⟩
  let byteSelector ← word m "node.byte-selector" (a+o.bitAtA) 1
  let bitSelector ← word m "node.bit-selector" (a+o.bitAtB) 1
  unless byteSelector == (cidr/8 ^^^ ((width/8-1)%8)) && bitSelector == 7-cidr%8 do
    throw ⟨"node.selectors", a, "child selector disagrees with CIDR and family"⟩
  let key ← if width == 32 then word m "node.key32" (a+o.bits) 4 else do
    let hi ← word m "node.key128.high" (a+o.bits) 8
    let lo ← word m "node.key128.low" (a+o.bits+8) 8
    pure (hi*2^64+lo)
  return {peer, children, cidr, width, key}

def reconstruct (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem) : Decode State := do
  unless o.nodeSize == AllowedipsLayout.nodeSize && o.peer == AllowedipsLayout.peer &&
      o.children == AllowedipsLayout.bit && o.cidr == AllowedipsLayout.cidr &&
      o.bitAtA == AllowedipsLayout.bit_at_a && o.bitAtB == AllowedipsLayout.bit_at_b &&
      o.bitlen == AllowedipsLayout.bitlen && o.bits == AllowedipsLayout.bits &&
      o.peerRefcount == Layouts.peer_refcount do throw ⟨"layout", 0, "trie layout drift"⟩
  for pairs in [names.nodes, names.peers] do
    unless (pairs.map Prod.fst).eraseDups.length == pairs.length &&
        (pairs.map Prod.snd).eraseDups.length == pairs.length do
      throw ⟨"interpretation", 0, "duplicate identity/address"⟩
  let ranges := names.nodes.map (fun (_, a) => (a, o.nodeSize)) ++
    names.peers.map (fun (_, a) => (a, Layouts.peerSize))
  for ((a, size), i) in ranges.zipIdx do
    unless 0 < a && a + size < 2^64 do throw ⟨"interpretation", a, "NULL/wrapping object"⟩
    for (b, size') in ranges.drop (i+1) do
      unless disjointRanges a size b size' do throw ⟨"interpretation", a, "overlapping objects"⟩
  let nodes ← names.nodes.mapM fun (id, a) => do return (id, ← decodeNode names o m a)
  let counts ← names.peers.mapM fun (id, a) => do
    return (id, ← word m s!"peer[{id}].refcount" (a+o.peerRefcount) 4)
  return {nodes, counts}

/-- A finite heap assertion, evaluated on the decoded state. Strictly increasing
CIDRs forbid cycles. The two roots are supplied call-environment identities;
this pilot does not claim their storage was reconstructed from device memory. -/
def heap (s : State) (roots : List (Option NodeId)) : Except String Unit := do
  for root in roots do
    if let some id := root then
      unless s.nodes.any (·.1 == id) do throw s!"trie.root: absent node {id}"
  let mut parents : List NodeId := []
  for (id, node) in s.nodes do
    for (child, bit) in node.children.toList.zipIdx do
      if let some next := child then
        let some (_, n) := s.nodes.find? (·.1 == next) | throw s!"trie.child: absent node {next}"
        if parents.contains next then throw s!"trie.parents: repeated child {next}"
        if roots.contains (some next) then throw s!"trie.parents: root {next} is also a child"
        parents := next :: parents
        unless n.width == node.width && node.cidr < n.cidr do
          throw s!"trie.measure: {id}->{next} does not increase CIDR in the same family"
        unless n.key / 2^(node.width-node.cidr) == node.key / 2^(node.width-node.cidr) do
          throw s!"trie.prefix: child {next} does not share parent {id}'s prefix"
        unless n.key / 2^(node.width-1-node.cidr) % 2 == bit do
          throw s!"trie.branch: child {next} is on the wrong side of {id}"

def Corresponds (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem) (d : Device) : Prop :=
  reconstruct names o m = .ok (target d)

def assertAt (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem) (w : World) : Except String Unit := do
  let some d := w.k.wg | throw "trie: mirror device missing"
  let actual ← (reconstruct names o m).mapError DecodeError.message
  let expected := target d
  unless actual.nodes == expected.nodes do
    throw s!"trie.nodes: binary={repr actual.nodes}, mirror={repr expected.nodes}"
  unless actual.counts == expected.counts do
    throw s!"trie.counts: binary={repr actual.counts}, mirror={repr expected.counts}"
  heap actual [d.peerAllowedips.root4, d.peerAllowedips.root6]

def address (names : List (Nat × Nat)) (id : Option Nat) : Except String Nat := do
  match id with
  | none => return 0
  | some id =>
    let some (_, a) := names.find? (·.1 == id) | throw s!"missing identity {id}"
    return a

end Binary.Pair.Trie
