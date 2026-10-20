import AllowedipsNodeRecordFields
import AllowedipsRootLists
import AllowedipsRootInternal

namespace Binary.Pair.Allowedips.NodeInit
open Leanux Leanux.WG Root

theorem attach_lists {names o s memory base cidr d pid owner}
    (related : Corresponds names o s.dmem d)
    (heapOk : heap names (target d) s.dmem=.ok ())
    (g : Geometry (names.allocated base) o) (nonnull : base≠0)
    (fresh : ∀ p ∈ names.trie.nodes, p.2≠base)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (zeroNext : word s.dmem "peer.list.next" (base+56) 8=.ok 0)
    (zeroPrev : word s.dmem "peer.list.prev" (base+64) 8=.ok 0)
    (checked : attach s=.ok (memory,base,cidr)) :
    ∀ current address count entries, (current,address) ∈ names.trie.peers →
      (current,count,entries) ∈ (target d).peers →
      (do
        let first ← word memory "peer.list.head" (address+1096) 8
        peerList (names.allocated base) memory (address+1096)
          ((names.allocated base).trie.nodes.length+1) first (address+1096) [])=
        .ok (if current=pid then entries++[names.nextNode] else entries) := by
  have layout : o.nodeSize=72 := (Trie.reconstruct_fields related.trie).layout.1
  have named := allocated_node names base
  have nb := g.bounded _ (node_allocation named)
  change base+o.nodeSize≤2^64 at nb
  rw [layout] at nb
  have baseNat : (UInt64.ofNat base).toNat=base := Nat.mod_eq_of_lt (by omega)
  have appended := append_effect g layout named (by exact peerNamed) checked
  have result := Root.append_lists (s:=rootView s base) related heapOk
    (by simpa only [rootView,baseNat] using g) (by simpa only [rootView,baseNat] using nonnull)
    (by simpa only [rootView,baseNat] using fresh) peerNamed hasPeer
    (by simpa only [rootView,baseNat] using zeroNext) (by simpa only [rootView,baseNat] using zeroPrev) appended
  simpa only [rootView,baseNat] using result

theorem attach_internal {names o s memory base cidr d pid owner current node}
    (related : Corresponds names o s.dmem d) (shape : heap names (target d) s.dmem=.ok ())
    (g : Geometry (names.allocated base) o)
    (fresh : ∀ p ∈ names.trie.nodes, p.2≠base)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (checked : attach s=.ok (memory,base,cidr))
    (member : (current,node) ∈ (target d).nodes) (internal : node.peer=none) :
    internalListCheck (names.allocated base) memory current=.ok () := by
  have layout : o.nodeSize=72 := (Trie.reconstruct_fields related.trie).layout.1
  have named := allocated_node names base
  have nb := g.bounded _ (node_allocation named)
  change base+o.nodeSize≤2^64 at nb
  rw [layout] at nb
  have baseNat : (UInt64.ofNat base).toNat=base := Nat.mod_eq_of_lt (by omega)
  have appended := append_effect g layout named (by exact peerNamed) checked
  have result := Root.append_internal (s:=rootView s base) related shape
    (by simpa only [rootView,baseNat] using g) (by simpa only [rootView,baseNat] using fresh)
    peerNamed hasPeer appended member internal
  simpa only [rootView,baseNat] using result

#print axioms attach_lists
#print axioms attach_internal
end Binary.Pair.Allowedips.NodeInit
