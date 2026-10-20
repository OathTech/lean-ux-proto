import AllowedipsNodeLocalFrame
import AllowedipsRootFrame

namespace Binary.Pair.Allowedips.NodeInit
open Root

theorem BoundaryFields.geometry {names world machine key cidr pid base d}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d) :
    Geometry (names.allocated base) nodeOffsets := by
  obtain ⟨_,_,extent,fresh,_⟩ := allocated_facts fields.allocated
  exact (Allowedips.geometry related).allocate (Nat.le_of_lt extent) fresh

theorem BoundaryFields.fresh {names world machine key cidr pid base}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base) :
    ∀ pair ∈ names.trie.nodes, pair.2≠base := by
  intro pair member same
  have apart := (allocated_facts fields.allocated).2.2.2.1 _ (node_allocation member)
  change disjointRanges base 72 pair.2 72=true at apart
  simp only [same,disjointRanges,Bool.or_self,decide_eq_true_eq] at apart
  omega

theorem BoundaryFields.stack_slice_apart {names o world machine key cidr pid base}
    (fields : BoundaryFields names o world machine key cidr pid base)
    {span : Span} (member : span ∈ [(base,72),(names.table,24)]++allocations names o)
    (offset size : Nat) (within : offset+size≤span.2) :
    ∀ a, InRange (.ofNat 64 (span.1+offset)) size a → ¬StackWrites machine.data.regs.rsp.toNat a := by
  intro a read ⟨writtenOffset,atOffset,written⟩
  have atStack : (machine.data.regs.rsp.toNat+writtenOffset,1) ∈
      [(machine.data.regs.rsp.toNat+36,1),(machine.data.regs.rsp.toNat+43,1),
        (machine.data.regs.rsp.toNat+44,1)] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at atOffset
    rcases atOffset with rfl|rfl|rfl <;> simp
  apply spansApart_sound fields.stackApart atStack member written
  obtain ⟨i,bound,equal⟩ := read
  refine ⟨offset+i,by omega,?_⟩
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal

theorem BoundaryFields.stack_allocation_apart {names world machine key cidr pid base}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    {span : Span} (member : span ∈ allocations (names.allocated base) nodeOffsets)
    (offset size : Nat) (within : offset+size≤span.2) :
    ∀ a, InRange (.ofNat 64 (span.1+offset)) size a → ¬StackWrites machine.data.regs.rsp.toNat a := by
  apply fields.stack_slice_apart (offset:=offset) (size:=size) _ within
  have oldOrFresh : span=(base,72) ∨ span ∈ allocations names nodeOffsets := by
    simpa only [allocations,Names.allocated,List.map_append,List.map_cons,List.map_nil,
      List.mem_append,List.mem_singleton,nodeOffsets,AllowedipsLayout.nodeSize,
      or_assoc,or_comm,or_left_comm] using member
  rcases oldOrFresh with rfl|old
  · simp
  · exact List.mem_append_right _ old

theorem BoundaryFields.old_field_apart {names world machine key cidr pid base d id address offset size}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (named : (id,address) ∈ names.trie.nodes) (within : offset+size≤56) :
    ∀ a, InRange (.ofNat 64 (address+offset)) size a → ¬EntryWrites names machine.data base a := by
  have g := fields.geometry related
  have oldNamed : (id,address) ∈ (names.allocated base).trie.nodes := List.mem_append_left _ named
  have freshNamed := allocated_node names base
  intro a inside written
  rcases written with fresh | lists | stack
  · exact g.slices_apart (node_allocation oldNamed) (node_allocation freshNamed)
      offset size 0 72 (by change offset+size≤72; omega) (by dsimp only; decide)
      (fun same => False.elim (fields.fresh _ named (congrArg Prod.fst same))) a inside
      (by simpa only [Nat.add_zero] using fresh)
  · exact node_before_list_apart g rfl oldNamed within a inside lists
  · exact fields.stack_allocation_apart (node_allocation oldNamed) offset size
      (by change offset+size≤72; omega) a inside stack

theorem BoundaryFields.old_node_frame {names world machine key cidr pid base d after id address value}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (named : (id,address) ∈ names.trie.nodes)
    (frame : EqualOutside (EntryWrites names machine.data base) machine.data.dmem after)
    (read : decodeNode names nodeOffsets machine.data.dmem id address=.ok value) :
    decodeNode (names.allocated base) nodeOffsets after id address=.ok value := by
  have words (offset size) (within : offset+size≤56) (path) :
      word after path (address+offset) size=word machine.data.dmem path (address+offset) size :=
    (Trie.word_frame frame path _ _ (fields.old_field_apart related named within)).symm
  have core : Trie.decodeNode names.trie nodeOffsets after address=
      Trie.decodeNode names.trie nodeOffsets machine.data.dmem address := by
    apply Trie.decodeNode_congr
    intro offset size field path
    exact words offset size (node_field_bounds related field).1 path
  have parent := words 48 8 (by decide) "node.parent"
  apply decodeNode_allocate
  simpa only [decodeNode,core,AllowedipsMutationLayout.parent_bit_packed,parent] using read

theorem BoundaryFields.table_field_apart {names world machine key cidr pid base d offset size}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d) (within : offset+size≤24) :
    ∀ a, InRange (.ofNat 64 (names.table+offset)) size a → ¬EntryWrites names machine.data base a := by
  have g := fields.geometry related
  intro a inside written
  rcases written with fresh | lists | stack
  · exact table_allocation_bytes fields.allocated g (node_allocation (allocated_node names base)) within
      (field:=0) (width:=72) (by dsimp only; decide) a inside (by simpa only [Nat.add_zero] using fresh)
  · exact table_lists_apart fields.allocated g rfl within a inside lists
  · exact fields.stack_slice_apart (span:=(names.table,24)) (by simp) offset size within a inside stack

theorem BoundaryFields.count_apart {names world machine key cidr pid base d current address}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (named : (current,address) ∈ names.trie.peers) :
    ∀ a, InRange (.ofNat 64 (address+Layouts.peer_refcount)) 4 a → ¬EntryWrites names machine.data base a := by
  have g := fields.geometry related
  have peerNamed : (current,address) ∈ (names.allocated base).trie.peers := named
  intro a inside written
  rcases written with fresh | lists | stack
  · exact g.slices_apart (peer_allocation peerNamed) (node_allocation (allocated_node names base))
      Layouts.peer_refcount 4 0 72 (by dsimp only; decide) (by dsimp only; decide)
      (fun _ => .inr (by decide))
      a inside (by simpa only [Nat.add_zero] using fresh)
  · exact peer_count_list_apart g rfl peerNamed a inside lists
  · exact fields.stack_allocation_apart (peer_allocation peerNamed) Layouts.peer_refcount 4
      (by dsimp only; decide) a inside stack

theorem BoundaryFields.initialization_lists_apart {names world machine key cidr pid base d}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d) :
    ∀ a, ListWrites (names.allocated base) a → ¬InitWrites base machine.data.regs.rsp.toNat a := by
  intro a list written
  rcases written with record | stack
  · exact node_before_list_apart (fields.geometry related) rfl (allocated_node names base)
      (offset:=0) (size:=56) (by decide) a (by simpa only [Nat.add_zero] using record) list
  · obtain ⟨link,slot,offset,which,inside⟩ := list
    cases slot with
    | node named =>
      exact fields.stack_allocation_apart (node_allocation named) (56+offset) 8
        (by change 56+offset+8≤72; rcases which with rfl|rfl <;> decide)
        a (by simpa only [Nat.add_assoc] using inside) stack
    | peer named =>
      exact fields.stack_allocation_apart (peer_allocation named) (1096+offset) 8
        (by dsimp only; rcases which with rfl|rfl <;> decide)
        a (by simpa only [Nat.add_assoc] using inside) stack

end Binary.Pair.Allowedips.NodeInit
