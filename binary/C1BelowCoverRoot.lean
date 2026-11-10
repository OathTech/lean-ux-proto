import C1BelowCoverReconstruct
import C1BelowSplitRoot

/-! Result C1, work package 3, covering path at the root (the sub-case trial
T2 left untreated): reconstruction after the two stores of
`connect_node(&newnode->bit[b], b, down)` and the publication of the fresh
node in the family's root slot. The root-publication lemmas are the generic
ones of the split path's port (`C1Split.connect_root_*`). -/
namespace Binary.Pair.Allowedips.C1Cover
open Leanux Leanux.WG Root

/-- The expected state: `down` hangs below the fresh node, the fresh node is
the root of its family. -/
def installedCoverRoot (v4 : Bool) (downId b key cidr width pid : Nat) (s : State) : State :=
  { table := if v4 then {s.table with root4:=some s.nextNode} else {s.table with root6:=some s.nextNode}
    nodes := s.nodes.map (reparent downId (.child s.nextNode b))++
      [(s.nextNode,{newNode key cidr width (some pid) with
        bit:=(newNode key cidr width (some pid)).bit.set! b (some downId),
        parent:=if v4 then Slot.root4 else Slot.root6})]
    peers := s.peers.map (appendOwner s.nextNode pid)
    nextNode := s.nextNode+1 }

theorem reconstruct_cover_root {names : Names} {world : World} {machine : MachineState}
    {key cidr pid base downId downBase b : Nat} {memory : DataMem} {d : Device} (v4 : Bool)
    (fields : NodeInit.BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (downNamed : (downId,downBase) ∈ names.trie.nodes) (downBit : b<2) :
    reconstruct (names.allocated base) nodeOffsets
      (connectMemory (connectMemory memory downBase (base+8+b*8) ((base+8+b*8) ||| b))
        base (names.table+C1Split.rootOffset v4) ((names.table+C1Split.rootOffset v4) ||| 2))=
      .ok (installedCoverRoot v4 downId b key cidr machine.data.regs.rbp.toNat pid (target d)) := by
  let n := names.allocated base
  let first := connectMemory memory downBase (base+8+b*8) ((base+8+b*8) ||| b)
  let after := connectMemory first base (n.table+C1Split.rootOffset v4) ((n.table+C1Split.rootOffset v4) ||| 2)
  have g := fields.geometry related
  have full := reconstruct_fields related
  have arena : C1Split.Arena n := C1Split.arena_of_valid fields.allocated
  have below := ids_below_counter full.valid
  have downNew : (downId,downBase) ∈ n.trie.nodes := List.mem_append_left _ downNamed
  have named := allocated_node names base
  have facts := allocated_facts fields.allocated
  have firstCore := cover_fresh_core (packed:=(base+8+b*8) ||| b) related g fields.fresh downBit downNamed pending.core
  have published := C1Split.connect_root_child (memory:=first) (childId:=names.nextNode) arena named v4 firstCore
  have freshRead : decodeNode n nodeOffsets after names.nextNode base=
      .ok (names.nextNode,{newNode key cidr machine.data.regs.rbp.toNat (some pid) with
        bit:=(newNode key cidr machine.data.regs.rbp.toNat (some pid)).bit.set! b (some downId),
        parent:=if v4 then Slot.root4 else Slot.root6}) := by
    simpa only [Trie.targetNode,newNode] using published.1
  have rootPointer (path : String) : Trie.pointer n.trie.nodes path base=.ok (some names.nextNode) :=
    pointer_named arena.addresses named (arena.positive _ named) path
  have keepTable (offset) (within : offset+8≤24)
      (different : offset+8≤C1Split.rootOffset v4 ∨ C1Split.rootOffset v4+8≤offset) (path) :
      word after path (names.table+offset) 8=word machine.data.dmem path (names.table+offset) 8 :=
    (C1Split.connect_root_table (n:=n) arena named v4 within different path).trans
    ((Trie.word_frame (connect_frame memory downBase (base+8+b*8) ((base+8+b*8) ||| b)) path _ _
      (connect_table_apart fields.allocated g downNew named downBit within)).symm.trans
      (pending.table offset 8 within path))
  obtain ⟨root4,root4Read,root4Pointer⟩ := full.root4
  obtain ⟨root6,root6Read,root6Pointer⟩ := full.root6
  let table : AllowedIps := if v4 then {d.peerAllowedips with root4:=some names.nextNode}
    else {d.peerAllowedips with root6:=some names.nextNode}
  have newRoot4 : ∃ raw, word after "table.root4" (names.table+AllowedipsMutationLayout.root4) 8=.ok raw ∧
      Trie.pointer n.trie.nodes "table.root4" raw=.ok table.root4 := by
    cases v4
    · exact ⟨root4,(keepTable 0 (by decide) (.inl (by decide)) "table.root4").trans root4Read,
        pointer_suffix root4Pointer⟩
    · exact ⟨base,word_path "table.root4" published.2,rootPointer "table.root4"⟩
  have newRoot6 : ∃ raw, word after "table.root6" (names.table+AllowedipsMutationLayout.root6) 8=.ok raw ∧
      Trie.pointer n.trie.nodes "table.root6" raw=.ok table.root6 := by
    cases v4
    · exact ⟨base,word_path "table.root6" published.2,rootPointer "table.root6"⟩
    · exact ⟨root6,(keepTable 8 (by decide) (.inr (by decide)) "table.root6").trans root6Read,
        pointer_suffix root6Pointer⟩
  have seqRead : word after "table.seq" (names.table+AllowedipsMutationLayout.seq) 8=.ok table.seq.toNat := by
    have kept := keepTable 16 (by decide) (.inr (by cases v4 <;> decide)) "table.seq"
    cases v4 <;> exact kept.trans full.seq
  have result := reconstruct_allocated (after:=after) (table:=table)
    (newNode:={newNode key cidr machine.data.regs.rbp.toNat (some pid) with
      bit:=(newNode key cidr machine.data.regs.rbp.toNat (some pid)).bit.set! b (some downId),
      parent:=if v4 then Slot.root4 else Slot.root6})
    (reparent downId (.child names.nextNode b)) (appendOwner names.nextNode pid)
    related fields.allocated newRoot4 newRoot6 seqRead
    (by
      rintro ⟨current,address⟩ member ⟨actual,node⟩ read
      have identity := (decodeNode_fields read).1
      dsimp only at identity
      subst actual
      have afterFirst := cover_down_old_node related g fields.fresh (by omega) facts.2.1 downBit
        downNamed member (pending.nodes _ member _ read)
      exact C1Split.connect_root_other arena named (List.mem_append_left _ member)
        (Nat.ne_of_lt (below _ member)) v4 afterFirst)
    freshRead (by
      rintro ⟨current,address⟩ member value read
      have peerNamed : (current,address) ∈ n.trie.peers := member
      rw [C1Split.connect_root_peer arena named peerNamed v4,
        connect_peer_frame g downNew named member downBit]
      exact pending.peers _ member _ read)
  have final : reconstruct n nodeOffsets after=
      .ok (installedCoverRoot v4 downId b key cidr machine.data.regs.rbp.toNat pid (target d)) := by
    simpa only [installedCoverRoot,n,←full.nextNode,target,table] using result
  exact final

#print axioms reconstruct_cover_root
end Binary.Pair.Allowedips.C1Cover
