import AllowedipsChildReconstruct

/-! Origin: trial T2, `binary-trials/t2/CoverReconstruct.lean` on `task/binary-trials` (unreviewed), copied
under the package prefix with the namespaces suffixed `C1Cover`; proofs unchanged. -/

/-! Trial T2: reconstruction after the four connection stores of the "covering"
insertion (`newnode->cidr == cidr`, non-NULL parent) of `add()`. -/
namespace Binary.Pair.Allowedips.C1Cover
open Leanux Leanux.WG Root

def reparent (downId : Nat) (slot : Slot) (entry : NodeId×AipNode) : NodeId×AipNode :=
  (entry.1,if entry.1=downId then {entry.2 with parent:=slot} else entry.2)

def coverUpdate (downId b parentId direction fresh : Nat) (entry : NodeId×AipNode) : NodeId×AipNode :=
  installChild parentId direction fresh (reparent downId (.child fresh b) entry)

def installedCover (downId b parentId direction key cidr width pid : Nat) (s : State) : State :=
  { s with
    nodes := s.nodes.map (coverUpdate downId b parentId direction s.nextNode)++
      [(s.nextNode,{newNode key cidr width (some pid) with
        bit:=(newNode key cidr width (some pid)).bit.set! b (some downId),
        parent:=.child parentId direction})]
    peers := s.peers.map (appendOwner s.nextNode pid)
    nextNode := s.nextNode+1 }

/-- First connection (`connect_node(&newnode->bit[b], b, down)`) seen from an
old record: only `down`'s packed parent changes. -/
theorem cover_down_old_node {names : Names} {entry : MachineData} {memory : DataMem} {d : Device}
    {base downId downBase b current address : Nat} {node : AipNode}
    (related : Corresponds names nodeOffsets entry.dmem d)
    (g : Geometry (names.allocated base) nodeOffsets)
    (fresh : ∀ pair ∈ names.trie.nodes, pair.2≠base)
    (positive : base≠0) (aligned : base%8=0) (bit : b<2)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (named : (current,address) ∈ names.trie.nodes)
    (read : decodeNode (names.allocated base) nodeOffsets memory current address=.ok (current,node)) :
    decodeNode (names.allocated base) nodeOffsets
      (connectMemory memory downBase (base+8+b*8) ((base+8+b*8) ||| b)) current address=
      .ok (reparent downId (.child names.nextNode b) (current,node)) := by
  have currentNamed : (current,address) ∈ (names.allocated base).trie.nodes := List.mem_append_left _ named
  have downNew : (downId,downBase) ∈ (names.allocated base).trie.nodes := List.mem_append_left _ downNamed
  have freshNamed := allocated_node names base
  have extent := g.bounded _ (node_allocation freshNamed)
  change base+72≤2^64 at extent
  have downExtent := g.bounded _ (node_allocation downNew)
  change downBase+72≤2^64 at downExtent
  have slotEq : base+8+b*8=base+(b+1)*8 := by omega
  by_cases same : current=downId
  · subst current
    have equal := Index.unique_first (Trie.reconstruct_fields related.trie).nodeIds named downNamed
    subst address
    unfold decodeNode at read
    obtain ⟨core,coreRead,read⟩ := bind_ok read
    obtain ⟨parentWord,parentRead,read⟩ := bind_ok read
    obtain ⟨slot,slotRead,read⟩ := bind_ok read
    cases Except.ok.inj read
    have parentDecoded : parent (names.allocated base) ((base+8+b*8) ||| b)=.ok (.child names.nextNode b) := by
      rw [slotEq]
      exact parent_child aligned bit (pointer_allocated "node.parent" positive fresh)
    have result := connect_record (names:=names.allocated base) (id:=downId) (by omega : downBase+56≤2^64)
      (by omega : base+8+b*8+8≤2^64)
      (Nat.or_lt_two_pow (by omega : base+8+b*8<2^64) (by omega : b<2^64))
      coreRead parentDecoded (by
        intro a old slotRead
        apply g.slices_apart (node_allocation downNew) (node_allocation freshNamed)
          0 56 (8+b*8) 8 (by dsimp only; decide) (by change 8+b*8+8≤72; omega)
          (fun same => False.elim (fresh _ downNamed (congrArg Prod.fst same))) a
          (by simpa only [Nat.add_zero] using old)
        simpa only [Nat.add_assoc] using slotRead)
    simpa only [reparent,ite_true] using result.1
  · have differentAddress : address≠downBase := by
      intro equal
      have first := find_address (name_addresses related).1 named
      have second := find_address (name_addresses related).1 downNamed
      rw [equal] at first
      exact same (congrArg Prod.fst (Option.some.inj (first.symm.trans second)))
    have keep : decodeNode (names.allocated base) nodeOffsets
        (connectMemory memory downBase (base+8+b*8) ((base+8+b*8) ||| b)) current address=
        decodeNode (names.allocated base) nodeOffsets memory current address := by
      unfold connectMemory
      have second : decodeNode (names.allocated base) nodeOffsets
          (write64 (write64 memory (downBase+48) ((base+8+b*8) ||| b)) (base+8+b*8) downBase) current address=
          decodeNode (names.allocated base) nodeOffsets
            (write64 memory (downBase+48) ((base+8+b*8) ||| b)) current address := by
        apply record_bytes_congr
        intro offset size within path
        apply word_write64_frame
        rw [Nat.add_assoc]
        exact g.slices_apart (node_allocation currentNamed) (node_allocation freshNamed)
          offset size (8+b*8) 8 (by change offset+size≤72; omega) (by change 8+b*8+8≤72; omega)
          (fun same => False.elim (fresh _ named (congrArg Prod.fst same)))
      have first : decodeNode (names.allocated base) nodeOffsets
          (write64 memory (downBase+48) ((base+8+b*8) ||| b)) current address=
          decodeNode (names.allocated base) nodeOffsets memory current address := by
        apply record_bytes_congr
        intro offset size within path
        apply word_write64_frame
        exact g.slices_apart (node_allocation currentNamed) (node_allocation downNew)
          offset size 48 8 (by change offset+size≤72; omega) (by dsimp only; decide)
          (fun same => False.elim (differentAddress (congrArg Prod.fst same)))
      exact second.trans first
    simpa only [reparent,ite_eq_right same] using keep.trans read

#print axioms cover_down_old_node

/-- The fresh record's core after the first connection: `bit[b]` now names `down`. -/
theorem cover_fresh_core {names : Names} {entry : MachineData} {memory : DataMem} {d : Device}
    {base downId downBase b packed : Nat} {node : Trie.Node}
    (related : Corresponds names nodeOffsets entry.dmem d)
    (g : Geometry (names.allocated base) nodeOffsets)
    (fresh : ∀ pair ∈ names.trie.nodes, pair.2≠base) (bit : b<2)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (core : Trie.decodeNode (names.allocated base).trie nodeOffsets memory base=.ok node) :
    Trie.decodeNode (names.allocated base).trie nodeOffsets
      (connectMemory memory downBase (base+8+b*8) packed) base=
      .ok {node with children:=node.children.set! b (some downId)} := by
  have downNew : (downId,downBase) ∈ (names.allocated base).trie.nodes := List.mem_append_left _ downNamed
  have freshNamed := allocated_node names base
  have extent := g.bounded _ (node_allocation freshNamed)
  change base+72≤2^64 at extent
  have downExtent := g.bounded _ (node_allocation downNew)
  change downBase+72≤2^64 at downExtent
  have middle : Trie.decodeNode (names.allocated base).trie nodeOffsets
      (write64 memory (downBase+48) packed) base=.ok node := by
    rw [←core]
    symm
    apply Trie.decodeNode_congr
    intro offset size field path
    have within : offset+size≤48 := by
      simp only [Trie.nodeSpans,nodeOffsets,AllowedipsLayout.peer,AllowedipsLayout.bit,
        AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,
        AllowedipsLayout.bitlen,AllowedipsLayout.bits,List.mem_cons,List.not_mem_nil,
        or_false,Prod.mk.injEq] at field
      omega
    symm
    apply word_write64_frame
    exact g.slices_apart (node_allocation freshNamed) (node_allocation downNew)
      offset size 48 8 (by change offset+size≤72; omega) (by dsimp only; decide)
      (fun same => False.elim (fresh _ downNamed (congrArg Prod.fst same).symm))
  have positive : 0<downBase := ((Trie.reconstruct_fields related.trie).nodeRange _ _ downNamed).1
  exact core_child_write bit (by omega) (by omega) middle
    (fun path => pointer_suffix (pointer_named (name_addresses related).1 downNamed positive path))

#print axioms cover_fresh_core

/-- The four connection stores of the covering insertion complete the
reconstruction of the whole allowed-IP projection from the pending state. -/
theorem reconstruct_cover_connect {names : Names} {world : World} {machine : MachineState}
    {key cidr pid base downId downBase parentId parentBase b direction : Nat}
    {memory : DataMem} {d : Device}
    (fields : NodeInit.BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    -- `down` is the non-NULL child (or root) the walk stopped above: a live old node.
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    -- the non-NULL `parent` of the covering case: the last node the walk matched.
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    -- both bits are results of `choose()`.
    (downBit : b<2) (bit : direction<2) :
    reconstruct (names.allocated base) nodeOffsets
      (connectMemory (connectMemory memory downBase (base+8+b*8) ((base+8+b*8) ||| b))
        base (parentBase+8+direction*8) ((parentBase+8+direction*8) ||| direction))=
      .ok (installedCover downId b parentId direction key cidr machine.data.regs.rbp.toNat pid (target d)) := by
  let n := names.allocated base
  let first := connectMemory memory downBase (base+8+b*8) ((base+8+b*8) ||| b)
  let slot := parentBase+8+direction*8
  let packed := (parentBase+(direction+1)*8) ||| direction
  let after := connectMemory first base slot packed
  have slotEq : parentBase+(direction+1)*8=slot := by dsimp only [slot]; omega
  have g := fields.geometry related
  have full := reconstruct_fields related
  have parentNew : (parentId,parentBase) ∈ n.trie.nodes := List.mem_append_left _ parentNamed
  have downNew : (downId,downBase) ∈ n.trie.nodes := List.mem_append_left _ downNamed
  have named := allocated_node names base
  have extent : base+72≤2^64 := g.bounded _ (node_allocation named)
  have parentExtent : parentBase+72≤2^64 := g.bounded _ (node_allocation parentNew)
  have facts := allocated_facts fields.allocated
  have positive := facts.1
  have aligned := validate_node_aligned full.valid parentNamed
  have parentPointer : Trie.pointer n.trie.nodes "node.parent" parentBase=.ok (some parentId) :=
    pointer_suffix (pointer_named (name_addresses related).1 parentNamed
      ((Trie.reconstruct_fields related.trie).nodeRange _ _ parentNamed).1 "node.parent")
  have parentRead := parent_child (names:=n) aligned bit parentPointer
  have firstCore := cover_fresh_core (packed:=(base+8+b*8) ||| b) related g fields.fresh downBit downNamed pending.core
  have freshRead := connect_record (id:=names.nextNode) (by omega : base+56≤2^64)
    (by omega : parentBase+(direction+1)*8+8≤2^64)
    (Nat.or_lt_two_pow (by omega : parentBase+(direction+1)*8<2^64) (by omega : direction<2^64))
    firstCore parentRead (by
      intro a fresh slotRead
      apply g.slices_apart (node_allocation named) (node_allocation parentNew)
        0 56 (8+direction*8) 8 (by dsimp only; decide) (by change 8+direction*8+8≤72; omega)
        (fun same => False.elim (fields.fresh _ parentNamed (congrArg Prod.fst same).symm)) a
        (by simpa only [Nat.add_zero] using fresh)
      have offsetEq : (direction+1)*8=8+direction*8 := by omega
      simpa only [offsetEq] using slotRead)
  have freshRead : decodeNode n nodeOffsets after names.nextNode base=
      .ok (names.nextNode,{newNode key cidr machine.data.regs.rbp.toNat (some pid) with
        bit:=(newNode key cidr machine.data.regs.rbp.toNat (some pid)).bit.set! b (some downId),
        parent:=.child parentId direction}) := by
    simpa only [after,first,slotEq,packed,Trie.targetNode,newNode] using freshRead.1
  have keepTable (offset size) (within : offset+size≤24) (path) :
      word after path (names.table+offset) size=word machine.data.dmem path (names.table+offset) size :=
    (Trie.word_frame (connect_frame first base slot packed) path _ _
      (connect_table_apart fields.allocated g named parentNew bit within)).symm.trans
    ((Trie.word_frame (connect_frame memory downBase (base+8+b*8) ((base+8+b*8) ||| b)) path _ _
      (connect_table_apart fields.allocated g downNew named downBit within)).symm.trans
      (pending.table offset size within path))
  obtain ⟨root4,root4Read,root4Pointer⟩ := full.root4
  obtain ⟨root6,root6Read,root6Pointer⟩ := full.root6
  have result := reconstruct_allocated (after:=after) (table:=d.peerAllowedips)
    (newNode:={newNode key cidr machine.data.regs.rbp.toNat (some pid) with
      bit:=(newNode key cidr machine.data.regs.rbp.toNat (some pid)).bit.set! b (some downId),
      parent:=.child parentId direction})
    (coverUpdate downId b parentId direction names.nextNode) (appendOwner names.nextNode pid)
    related fields.allocated
    ⟨root4,(keepTable 0 8 (by decide) "table.root4").trans root4Read,pointer_suffix root4Pointer⟩
    ⟨root6,(keepTable 8 8 (by decide) "table.root6").trans root6Read,pointer_suffix root6Pointer⟩
    ((keepTable 16 8 (by decide) "table.seq").trans full.seq)
    (by
      rintro ⟨current,address⟩ member ⟨actual,node⟩ read
      have identity := (decodeNode_fields read).1
      dsimp only at identity
      subst actual
      have afterFirst := cover_down_old_node related g fields.fresh (by omega) facts.2.1 downBit
        downNamed member (pending.nodes _ member _ read)
      exact connect_old_node related g fields.fresh (by omega) bit parentNamed member afterFirst)
    freshRead (by
      rintro ⟨current,address⟩ member value read
      rw [connect_peer_frame g named parentNew member bit,
        connect_peer_frame g downNew named member downBit]
      exact pending.peers _ member _ read)
  have reconstructed : reconstruct n nodeOffsets after=
      .ok (installedCover downId b parentId direction key cidr machine.data.regs.rbp.toNat pid (target d)) := by
    simpa only [installedCover,n,←full.nextNode,target] using result
  have packedEq : packed=(parentBase+8+direction*8) ||| direction := by
    dsimp only [packed]
    rw [slotEq]
  rw [←packedEq]
  exact reconstructed

#print axioms reconstruct_cover_connect
end Binary.Pair.Allowedips.C1Cover
