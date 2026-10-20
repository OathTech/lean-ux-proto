import AllowedipsChildConnectNodes
import AllowedipsConnectFrame
import AllowedipsChildParent

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG Root

def installedChild (parentId direction key cidr width pid : Nat) (s : State) : State :=
  { s with
    nodes := s.nodes.map (installChild parentId direction s.nextNode)++
      [(s.nextNode,{newNode key cidr width (some pid) with parent:=.child parentId direction})]
    peers := s.peers.map (appendOwner s.nextNode pid)
    nextNode := s.nextNode+1 }

/-- The two connection stores complete reconstruction of the entire allowed-IP
projection after the proved pending initialization. This data lemma is later
composed with the executed publication and the actual source child update. -/
theorem reconstruct_child_connect {names : Names} {world : World} {machine : MachineState}
    {key cidr pid base parentId parentBase direction : Nat} {memory : DataMem} {d : Device}
    (fields : NodeInit.BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes) (bit : direction<2) :
    reconstruct (names.allocated base) nodeOffsets
      (connectMemory memory base (parentBase+(direction+1)*8) ((parentBase+(direction+1)*8) ||| direction))=
      .ok (installedChild parentId direction key cidr machine.data.regs.rbp.toNat pid (target d)) := by
  let n := names.allocated base
  let slot := parentBase+8+direction*8
  let packed := (parentBase+(direction+1)*8) ||| direction
  let after := connectMemory memory base slot packed
  have slotEq : parentBase+(direction+1)*8=slot := by dsimp only [slot]; omega
  have g := fields.geometry related
  have full := reconstruct_fields related
  have parentNew : (parentId,parentBase) ∈ n.trie.nodes := List.mem_append_left _ parentNamed
  have named := allocated_node names base
  have extent : base+72≤2^64 := g.bounded _ (node_allocation named)
  have parentExtent : parentBase+72≤2^64 := g.bounded _ (node_allocation parentNew)
  have positive := (allocated_facts fields.allocated).1
  have aligned := validate_node_aligned full.valid parentNamed
  have parentPointer : Trie.pointer n.trie.nodes "node.parent" parentBase=.ok (some parentId) :=
    pointer_suffix (pointer_named (name_addresses related).1 parentNamed
      ((Trie.reconstruct_fields related.trie).nodeRange _ _ parentNamed).1 "node.parent")
  have parentRead := parent_child (names:=n) aligned bit parentPointer
  have freshRead := connect_record (id:=names.nextNode) (by omega : base+56≤2^64)
    (by omega : parentBase+(direction+1)*8+8≤2^64)
    (Nat.or_lt_two_pow (by omega : parentBase+(direction+1)*8<2^64) (by omega : direction<2^64))
    pending.core parentRead (by
      intro a fresh slotRead
      apply g.slices_apart (node_allocation named) (node_allocation parentNew)
        0 56 (8+direction*8) 8 (by dsimp only; decide) (by change 8+direction*8+8≤72; omega)
        (fun same => False.elim (fields.fresh _ parentNamed (congrArg Prod.fst same).symm)) a
        (by simpa only [Nat.add_zero] using fresh)
      have offsetEq : (direction+1)*8=8+direction*8 := by omega
      simpa only [offsetEq] using slotRead)
  have freshRead : decodeNode n nodeOffsets after names.nextNode base=
      .ok (names.nextNode,{newNode key cidr machine.data.regs.rbp.toNat (some pid) with parent:=.child parentId direction}) := by
    simpa only [after,slotEq,packed,Trie.targetNode,newNode] using freshRead.1
  have frame := connect_frame memory base slot packed
  have keepTable (offset size) (within : offset+size≤24) (path) :
      word after path (names.table+offset) size=word machine.data.dmem path (names.table+offset) size :=
    (Trie.word_frame frame path _ _ (connect_table_apart fields.allocated g named parentNew bit within)).symm.trans
      (pending.table offset size within path)
  obtain ⟨root4,root4Read,root4Pointer⟩ := full.root4
  obtain ⟨root6,root6Read,root6Pointer⟩ := full.root6
  have result := reconstruct_allocated (after:=after) (table:=d.peerAllowedips)
    (newNode:={newNode key cidr machine.data.regs.rbp.toNat (some pid) with parent:=.child parentId direction})
    (installChild parentId direction names.nextNode) (appendOwner names.nextNode pid)
    related fields.allocated
    ⟨root4,(keepTable 0 8 (by decide) "table.root4").trans root4Read,pointer_suffix root4Pointer⟩
    ⟨root6,(keepTable 8 8 (by decide) "table.root6").trans root6Read,pointer_suffix root6Pointer⟩
    ((keepTable 16 8 (by decide) "table.seq").trans full.seq)
    (by
      rintro ⟨current,address⟩ member ⟨actual,node⟩ read
      have identity := (decodeNode_fields read).1
      dsimp only at identity
      subst actual
      exact connect_old_node related g fields.fresh (by omega) bit parentNamed member (pending.nodes _ member _ read))
    freshRead (by
      rintro ⟨current,address⟩ member value read
      rw [connect_peer_frame g named parentNew member bit]
      exact pending.peers _ member _ read)
  have reconstructed : reconstruct n nodeOffsets after=
      .ok (installedChild parentId direction key cidr machine.data.regs.rbp.toNat pid (target d)) := by
    simpa only [installedChild,n,←full.nextNode,target] using result
  simpa only [n,after,packed,←slotEq] using reconstructed

#print axioms reconstruct_child_connect
end Binary.Pair.Allowedips
