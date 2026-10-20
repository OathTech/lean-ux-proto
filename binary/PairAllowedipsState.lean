import PairTrie
import AllowedipsMutationLayout

/-! The executable allowed-IPs projection. Reconstruction only reads physical
memory and the allocation-name interpretation; it never reads a source state.
Allocation counters are ghost state updated at successful allocator events. -/
namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

structure Names where
  table : Nat
  trie : Trie.Names
  nextNode : Nat
  deriving Repr

structure State where
  table : AllowedIps
  nodes : List (NodeId × AipNode)
  peers : List (PeerId × Nat × List NodeId)
  nextNode : Nat
  deriving Repr, BEq

def target (d : Device) : State :=
  ⟨d.peerAllowedips, d.nodes.toList,
    d.peers.toList.map (fun (id,p) => (id,p.refcount,p.allowedipsList)), d.nextNode⟩

def parent (names : Names) (a : Nat) : Decode Slot := do
  let tag := a % 4
  let slot := a - tag
  if tag == 2 then
    if slot == names.table + AllowedipsMutationLayout.root4 then return .root4
    if slot == names.table + AllowedipsMutationLayout.root6 then return .root6
    throw ⟨"node.parent", a, "unknown root slot"⟩
  unless tag < 2 && slot ≥ AllowedipsLayout.bit + 8*tag do
    throw ⟨"node.parent", a, "invalid packed child slot"⟩
  let p ← Trie.pointer names.trie.nodes "node.parent" (slot-AllowedipsLayout.bit-8*tag)
  let some id := p | throw ⟨"node.parent", a, "NULL parent"⟩
  return .child id tag

def peerList (names : Names) (m : DataMem) (head : Nat) :
    Nat → Nat → Nat → List Nat → Decode (List NodeId)
  | 0, _, _, _ => .error ⟨"peer.list", head, "traversal exhausted"⟩
  | fuel+1, link, previous, seen =>
    if !(link == head || names.trie.nodes.any (fun (_,a) => link == a+AllowedipsMutationLayout.peer_list)) then
      .error ⟨"peer.list",link,"unregistered embedded link"⟩
    else do
      let back ← word m "peer.list.prev" (link+8) 8
      unless back == previous do throw ⟨"peer.list.prev",link,"broken backlink"⟩
      if link == head then return []
      if seen.contains link then throw ⟨"peer.list",link,"cycle"⟩
      unless link ≥ AllowedipsMutationLayout.peer_list do
        throw ⟨"peer.list",link,"invalid embedded link"⟩
      let some id ← Trie.pointer names.trie.nodes "peer.list.node"
          (link-AllowedipsMutationLayout.peer_list)
        | throw ⟨"peer.list.node",link,"NULL owner"⟩
      let next ← word m "peer.list.next" link 8
      let tail ← peerList names m head fuel next link (link::seen)
      return id::tail

def validate (names : Names) (o : AllowedipsProbe.Offsets) : Decode Unit := do
  Trie.validate names.trie o
  unless 0 < names.table && names.table % 8 == 0 &&
      names.table+AllowedipsMutationLayout.tableSize < 2^64 do
    throw ⟨"table", names.table, "NULL, unaligned or wrapping table"⟩
  for (_,a) in names.trie.nodes do
    unless a % 8 == 0 do throw ⟨"node",a,"unaligned allocation"⟩
  for (id,_) in names.trie.nodes do
    unless id < names.nextNode do throw ⟨"names.nextNode",id,"identity beyond allocation counter"⟩
  for (a,size) in names.trie.nodes.map (fun (_,a) => (a,o.nodeSize)) ++
      names.trie.peers.map (fun (_,a) => (a,Layouts.peerSize)) do
    unless disjointRanges a size names.table AllowedipsMutationLayout.tableSize do
      throw ⟨"table",a,"allocation overlaps table"⟩

def decodeNode (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem)
    (id : NodeId) (a : Nat) : Decode (NodeId × AipNode) := do
  let n ← Trie.decodeNode names.trie o m a
  let slot ← parent names (← word m "node.parent" (a+AllowedipsMutationLayout.parent_bit_packed) 8)
  let node : AipNode := {
    peer := n.peer, bit := n.children, cidr := n.cidr, bitlen := n.width,
    bits := n.key, parent := slot}
  return (id,node)

def decodePeer (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem)
    (id : PeerId) (a : Nat) : Decode (PeerId × Nat × List NodeId) := do
  let count ← word m "peer.refcount" (a+o.peerRefcount) 4
  let head := a+AllowedipsMutationLayout.allowedips_list
  let first ← word m "peer.list.head" head 8
  let list ← peerList names m head (names.trie.nodes.length+1) first head []
  return (id,count,list)

def reconstruct (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem) : Decode State := do
  validate names o
  let root4 ← Trie.pointer names.trie.nodes "table.root4"
    (← word m "table.root4" (names.table+AllowedipsMutationLayout.root4) 8)
  let root6 ← Trie.pointer names.trie.nodes "table.root6"
    (← word m "table.root6" (names.table+AllowedipsMutationLayout.root6) 8)
  let seq ← word m "table.seq" (names.table+AllowedipsMutationLayout.seq) 8
  let nodes ← names.trie.nodes.mapM fun (id,a) => decodeNode names o m id a
  let peers ← names.trie.peers.mapM fun (id,a) => decodePeer names o m id a
  return ⟨{root4,root6,seq},nodes,peers,names.nextNode⟩

/-- Structural assertion, separate from the reconstruction equation. Every live
node has exactly one incoming root/child edge, with the matching packed parent;
peer membership is exact, and internal-node list heads are initialized. -/
def heap (names : Names) (s : State) (m : DataMem) : Except String Unit := do
  Trie.heap ⟨s.nodes.map (fun (id,n) => (id,Trie.targetNode n)),
    s.peers.map (fun (id,count,_) => (id,count))⟩ [s.table.root4,s.table.root6]
  for (id,n) in s.nodes do
    let roots := [(s.table.root4,Slot.root4,32),(s.table.root6,Slot.root6,128)]
    let mut incoming := []
    for (root,slot,width) in roots do
      if root == some id then
        unless n.bitlen == width do throw "heap.root-family"
        incoming := slot::incoming
    for (pid,p) in s.nodes do
      for (child,bit) in p.bit.toList.zipIdx do
        if child == some id then incoming := .child pid bit::incoming
    unless incoming == [n.parent] do throw s!"heap.parent[{id}]: {repr incoming}"
    let owners := s.peers.flatMap fun (pid,_,xs) => xs.filterMap fun x => if x == id then some pid else none
    unless owners == n.peer.toList do throw s!"heap.peer-membership[{id}]"
    if n.peer.isNone then
      let a ← Trie.address names.trie.nodes (some id)
      let head := a+AllowedipsMutationLayout.peer_list
      unless (← readNat ⟨{dmem := m},0⟩ head 8) == head &&
          (← readNat ⟨{dmem := m},0⟩ (head+8) 8) == head do throw "heap.internal-list"

def Corresponds (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem) (d : Device) : Prop :=
  reconstruct names o m = .ok (target d)

def assertAt (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem) (w : World) : Except String Unit := do
  let some d := w.wg.dev | throw "allowedips: missing mirror device"
  let actual ← (reconstruct names o m).mapError DecodeError.message
  let expected := target d
  unless actual.table == expected.table do throw s!"allowedips.table: {repr actual.table} != {repr expected.table}"
  unless actual.nodes == expected.nodes do throw s!"allowedips.nodes: {repr actual.nodes} != {repr expected.nodes}"
  unless actual.peers == expected.peers do throw s!"allowedips.peers: {repr actual.peers} != {repr expected.peers}"
  unless actual.nextNode == expected.nextNode do throw "allowedips.allocation-counter"
  heap names actual m

end Binary.Pair.Allowedips
