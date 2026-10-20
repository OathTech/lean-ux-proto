import AllowedipsChildRecordUpdate
import AllowedipsRecordBytes
import AllowedipsNodePending

namespace Binary.Pair.Allowedips
open Root Leanux Leanux.WG

def installChild (parentId direction fresh : Nat) (entry : NodeId×AipNode) : NodeId×AipNode :=
  (entry.1,if entry.1=parentId then {entry.2 with bit:=entry.2.bit.set! direction (some fresh)} else entry.2)

/-- Complete old-record update of the two physical connection stores.
Freshness and parent identity come from the established allocation names. -/
theorem connect_old_node {names : Names} {entry : MachineData} {memory : DataMem} {d : Device}
    {base parentId parentBase direction current address packed : Nat} {node : AipNode}
    (related : Corresponds names nodeOffsets entry.dmem d)
    (g : Geometry (names.allocated base) nodeOffsets)
    (fresh : ∀ pair ∈ names.trie.nodes, pair.2≠base)
    (positive : base≠0) (bit : direction<2)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (named : (current,address) ∈ names.trie.nodes)
    (read : decodeNode (names.allocated base) nodeOffsets memory current address=.ok (current,node)) :
    decodeNode (names.allocated base) nodeOffsets
      (connectMemory memory base (parentBase+8+direction*8) packed) current address=
      .ok (installChild parentId direction names.nextNode (current,node)) := by
  have currentNamed : (current,address) ∈ (names.allocated base).trie.nodes := List.mem_append_left _ named
  have freshNamed := allocated_node names base
  have keepFresh : decodeNode (names.allocated base) nodeOffsets (write64 memory (base+48) packed) current address=
      decodeNode (names.allocated base) nodeOffsets memory current address := by
    apply record_bytes_congr
    intro offset size within path
    apply word_write64_frame
    exact g.slices_apart (node_allocation currentNamed) (node_allocation freshNamed)
      offset size 48 8 (by change offset+size≤72; omega) (by dsimp only; decide)
      (fun same => False.elim (fresh _ named (congrArg Prod.fst same)))
  have afterFresh := keepFresh.trans read
  have small : base<2^64 := by
    have extent := g.bounded _ (node_allocation freshNamed)
    change base+72≤2^64 at extent
    omega
  unfold connectMemory
  by_cases same : current=parentId
  · subst current
    have equal := Index.unique_first (Trie.reconstruct_fields related.trie).nodeIds named parentNamed
    subst address
    have extent := g.bounded _ (node_allocation (names:=names.allocated base) (List.mem_append_left _ parentNamed))
    change parentBase+72≤2^64 at extent
    have result := record_child_write bit (by omega) small afterFresh
      (fun path => pointer_allocated path positive fresh)
    simpa only [installChild,ite_true] using result
  · have keepParent : decodeNode (names.allocated base) nodeOffsets
        (write64 (write64 memory (base+48) packed) (parentBase+8+direction*8) base) current address=
        decodeNode (names.allocated base) nodeOffsets (write64 memory (base+48) packed) current address := by
      apply record_bytes_congr
      intro offset size within path
      apply word_write64_frame
      rw [Nat.add_assoc]
      apply g.slices_apart (node_allocation currentNamed)
        (node_allocation (names:=names.allocated base) (List.mem_append_left _ parentNamed)) offset size (8+direction*8) 8
        (by change offset+size≤72; omega) (by change 8+direction*8+8≤72; omega)
      intro equal
      have addresses := congrArg Prod.fst equal
      have first := find_address (name_addresses related).1 named
      have second := find_address (name_addresses related).1 parentNamed
      dsimp only at addresses
      rw [addresses] at first
      exact False.elim (same (congrArg Prod.fst (Option.some.inj (first.symm.trans second))))
    simpa only [installChild,ite_eq_right same] using keepParent.trans afterFresh

#print axioms connect_old_node
end Binary.Pair.Allowedips
