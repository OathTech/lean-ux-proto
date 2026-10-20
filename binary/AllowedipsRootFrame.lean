import AllowedipsRootInitFrame
import AllowedipsAllocationTarget

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG

/-- Footprint of the whole successful initialization tail. The list locations
are resolved from physical ownership, and publication's slot from its load. -/
def Writes (names : Names) (base slot : Nat) (a : BitVec 64) : Prop :=
  ListWrites names a ∨ InitWrites base slot a

/-- Existing record fields are outside the fresh allocation, list links and
root slot. This is derived from the original relation and extended ownership,
without requiring that the not-yet-initialized allocation already decode. -/
theorem old_field_apart {names o entry d newBase id base offset size slot}
    (related : Corresponds names o entry d)
    (g : Geometry (names.allocated newBase) o)
    (fresh : ∀ p ∈ names.trie.nodes, p.2≠newBase)
    (named : (id,base) ∈ names.trie.nodes) (within : offset+size≤56)
    (rootSlot : slot=names.table ∨ slot=names.table+8) :
    ∀ a, InRange (.ofNat 64 (base+offset)) size a →
      ¬Writes (names.allocated newBase) newBase slot a := by
  have layout : o.nodeSize=72 := (Trie.reconstruct_fields related.trie).layout.1
  have oldNamed : (id,base) ∈ (names.allocated newBase).trie.nodes := by
    exact List.mem_append_left _ named
  have newNamed := allocated_node names newBase
  intro a inside written
  rcases written with lists|record|root
  · exact node_before_list_apart g layout oldNamed within a inside lists
  · have apart := g.slices_apart (node_allocation oldNamed) (node_allocation newNamed)
      offset size 0 56 (by dsimp only; rw [layout]; omega) (by dsimp only; rw [layout]; decide)
      (fun equal => False.elim (fresh (id,base) named (congrArg Prod.fst equal)))
    exact apart a inside (by simpa only [Nat.add_zero] using record)
  · rcases rootSlot with rfl|rfl
    · exact table_allocation_apart related (node_allocation named) (offset:=0) (size:=8)
        (by decide) (field:=offset) (width:=size) (by dsimp only; rw [layout]; omega)
        a (by simpa only [Nat.add_zero] using root) inside
    · exact table_allocation_apart related (node_allocation named) (offset:=8) (size:=8)
        (by decide) (field:=offset) (width:=size) (by dsimp only; rw [layout]; omega)
        a root inside

theorem old_node_frame {names o entry before after d newBase id base slot value}
    (related : Corresponds names o entry d)
    (g : Geometry (names.allocated newBase) o)
    (fresh : ∀ p ∈ names.trie.nodes, p.2≠newBase)
    (named : (id,base) ∈ names.trie.nodes)
    (rootSlot : slot=names.table ∨ slot=names.table+8)
    (frame : EqualOutside (Writes (names.allocated newBase) newBase slot) before after)
    (decoded : decodeNode names o before id base=.ok value) :
    decodeNode (names.allocated newBase) o after id base=.ok value := by
  have words (offset size) (within : offset+size≤56) (path) :
      word after path (base+offset) size=word before path (base+offset) size :=
    (Trie.word_frame frame path _ _ (old_field_apart related g fresh named within rootSlot)).symm
  have core : Trie.decodeNode names.trie o after base=Trie.decodeNode names.trie o before base := by
    apply Trie.decodeNode_congr
    intro offset size field path
    exact words offset size (node_field_bounds related field).1 path
  have parent := words 48 8 (by decide) "node.parent"
  apply decodeNode_allocate
  simpa only [decodeNode,core,AllowedipsMutationLayout.parent_bit_packed,parent] using decoded

#print axioms old_node_frame
end Binary.Pair.Allowedips.Root
