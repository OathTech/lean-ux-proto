import C1BelowSplitHeapMemory

/- Origin: trial source binary-trials/t5/T5Root.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 1, NULL-parent subcase (data only): the internal node is
published in the root slot (`rcu_assign_pointer(*trie, node)`). -/
namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG Root

def rootOffset (v4 : Bool) : Nat := if v4 then 0 else 8

theorem table_facts {n : Names} (valid : validate n nodeOffsets=.ok ()) :
    (0<n.table ∧ n.table%8=0) ∧ n.table+24<2^64 := by
  unfold validate at valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨table,_⟩ := check_ok _ _ _ _ valid
  have tableOriginal : (0<n.table ∧ n.table%8=0) ∧
      n.table+AllowedipsMutationLayout.tableSize<2^64 := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using table
  exact tableOriginal

theorem parent_rootSlot {n : Names} (aligned : n.table%8=0) (v4 : Bool) :
    parent n ((n.table+rootOffset v4) ||| 2)=.ok (if v4 then Slot.root4 else Slot.root6) := by
  cases v4
  · exact parent_root6 n aligned
  · exact parent_root4 n aligned

theorem listWrites_allocation {n : Names} {a : BitVec 64} (written : ListWrites n a) :
    ∃ span ∈ allocations n nodeOffsets, InRange (.ofNat 64 span.1) span.2 a := by
  obtain ⟨link,slot,offset,which,inside⟩ := written
  cases slot with
  | node named =>
    exact ⟨_,node_allocation named,inRange_within (offset:=56+offset) (size:=8) (total:=72)
      (by rcases which with rfl|rfl <;> decide) (by simpa only [Nat.add_assoc] using inside)⟩
  | peer named =>
    exact ⟨_,peer_allocation named,inRange_within (offset:=1096+offset) (size:=8) (total:=1520)
      (by rcases which with rfl|rfl <;> decide) (by simpa only [Nat.add_assoc] using inside)⟩

theorem span_root_apart {n : Names} (arena : Arena n) {span : Span}
    (member : span ∈ allocations n nodeOffsets) (v4 : Bool) :
    ∀ a, InRange (.ofNat 64 span.1) span.2 a → ¬InRange (.ofNat 64 (n.table+rootOffset v4)) 8 a :=
  fun a inSpan inTable => table_allocation_bytes arena.valid arena.geometry member
    (offset:=rootOffset v4) (size:=8) (by cases v4 <;> decide) (field:=0) (width:=span.2) (by omega)
    a inTable (by simpa only [Nat.add_zero] using inSpan)

theorem node_root_apart {n : Names} (arena : Arena n) {id address offset size : Nat}
    (named : (id,address) ∈ n.trie.nodes) (within : offset+size≤72) (v4 : Bool) :
    ∀ a, InRange (.ofNat 64 (address+offset)) size a → ¬InRange (.ofNat 64 (n.table+rootOffset v4)) 8 a :=
  fun a inNode => span_root_apart arena (node_allocation named) v4 a (inRange_within (total:=72) within inNode)

/-- The root publication seen from any other fully decoded record: nothing changes. -/
theorem connect_root_other {n : Names} {memory : DataMem}
    {childId childBase current address packed : Nat} {entry : NodeId×AipNode}
    (arena : Arena n) (childNamed : (childId,childBase) ∈ n.trie.nodes)
    (named : (current,address) ∈ n.trie.nodes) (different : current≠childId) (v4 : Bool)
    (read : decodeNode n nodeOffsets memory current address=.ok entry) :
    decodeNode n nodeOffsets (connectMemory memory childBase (n.table+rootOffset v4) packed)
      current address=.ok entry := by
  rw [←read]
  apply record_bytes_congr
  intro offset size within path
  unfold connectMemory
  refine (word_write64_frame _ _ _ _ _ _ (node_root_apart arena named (by omega) v4)).trans
    (word_write64_frame _ _ _ _ _ _ ?_)
  exact arena.geometry.slices_apart (node_allocation named) (node_allocation childNamed)
    offset size 48 8 (by change offset+size≤72; omega) (by dsimp only; decide)
    (fun equal => False.elim (arena.address_ne named childNamed different (congrArg Prod.fst equal)))

/-- The published record, from its core alone, and the root word. -/
theorem connect_root_child {n : Names} {memory : DataMem} {childId childBase : Nat} {core : Trie.Node}
    (arena : Arena n) (childNamed : (childId,childBase) ∈ n.trie.nodes) (v4 : Bool)
    (coreRead : Trie.decodeNode n.trie nodeOffsets memory childBase=.ok core) :
    decodeNode n nodeOffsets
      (connectMemory memory childBase (n.table+rootOffset v4) ((n.table+rootOffset v4) ||| 2))
      childId childBase=
      .ok (childId,({
        peer:=core.peer,bit:=core.children,cidr:=core.cidr,bitlen:=core.width,
        bits:=core.key,parent:=if v4 then Slot.root4 else Slot.root6} : AipNode)) ∧
    word (connectMemory memory childBase (n.table+rootOffset v4) ((n.table+rootOffset v4) ||| 2))
      "node.link" (n.table+rootOffset v4) 8=.ok childBase := by
  have facts := table_facts arena.valid
  have childExtent : childBase+72≤2^64 := arena.geometry.bounded _ (node_allocation childNamed)
  have offBound : rootOffset v4+8≤24 := by cases v4 <;> decide
  exact connect_record (names:=n) (id:=childId) (by omega) (by omega : n.table+rootOffset v4+8≤2^64)
    (Nat.or_lt_two_pow (by omega) (by decide)) coreRead (parent_rootSlot facts.1.2 v4)
    (fun a inNode => node_root_apart arena childNamed (offset:=0) (size:=56) (by decide) v4 a
      (by simpa only [Nat.add_zero] using inNode))

theorem connect_root_peer {n : Names} {m : DataMem} {childId childBase pid peer packed : Nat}
    (arena : Arena n) (childNamed : (childId,childBase) ∈ n.trie.nodes)
    (peerNamed : (pid,peer) ∈ n.trie.peers) (v4 : Bool) :
    decodePeer n nodeOffsets (connectMemory m childBase (n.table+rootOffset v4) packed) pid peer=
      decodePeer n nodeOffsets m pid peer := by
  have g := arena.geometry
  have frame := connect_frame m childBase (n.table+rootOffset v4) packed
  have count := Trie.word_frame frame "peer.refcount" (peer+Layouts.peer_refcount) 4 (by
    intro a read written
    rcases written with fresh|slot
    · exact g.slices_apart (peer_allocation peerNamed) (node_allocation childNamed)
        Layouts.peer_refcount 4 48 8 (by dsimp only; decide) (by dsimp only; decide)
        (fun _ => .inr (by decide)) a read fresh
    · exact span_root_apart arena (peer_allocation peerNamed) v4 a
        (inRange_within (total:=1520) (by decide) read) slot)
  have lists := list_read_frame (fuel:=n.trie.nodes.length+1) frame (by
    intro a list written
    rcases written with fresh|slot
    · exact node_before_list_apart g rfl childNamed (offset:=48) (size:=8) (by decide) a fresh list
    · obtain ⟨span,member,inSpan⟩ := listWrites_allocation list
      exact span_root_apart arena member v4 a inSpan slot) (.peer peerNamed)
  exact peer_decoder_congr count.symm lists.symm

theorem connect_root_table {n : Names} {m : DataMem} {childId childBase packed offset : Nat}
    (arena : Arena n) (childNamed : (childId,childBase) ∈ n.trie.nodes) (v4 : Bool)
    (within : offset+8≤24) (different : offset+8≤rootOffset v4 ∨ rootOffset v4+8≤offset) (path : String) :
    word (connectMemory m childBase (n.table+rootOffset v4) packed) path (n.table+offset) 8=
      word m path (n.table+offset) 8 := by
  have offBound : rootOffset v4+8≤24 := by cases v4 <;> decide
  unfold connectMemory
  refine (word_write64_frame _ _ _ _ _ _ ?_).trans (word_write64_frame _ _ _ _ _ _ ?_)
  · intro a inside
    rw [BitVec.ofNat_add] at inside ⊢
    exact InRange.offset_disjoint _ offset 8 (rootOffset v4) 8 (by omega) (by omega) different a inside
  · exact fun a inTable inNode => table_allocation_bytes arena.valid arena.geometry
      (node_allocation childNamed) within (field:=48) (width:=8) (by dsimp only; decide) a inTable inNode

#print axioms connect_root_other
#print axioms connect_root_child
#print axioms connect_root_peer
#print axioms connect_root_table

def installedIntermediateRoot (v4 : Bool) (downId b1 b2 key cidr common width pid : Nat) (s : State) : State :=
  { table := if v4 then {s.table with root4:=some (s.nextNode+1)} else {s.table with root6:=some (s.nextNode+1)}
    nodes := s.nodes.map (connectUpdate downId (s.nextNode+1) b1)++
      [(s.nextNode,{newNode key cidr width (some pid) with parent:=.child (s.nextNode+1) b2})]++
      [(s.nextNode+1,{newNode key common width none with
        bit:=((newNode key common width none).bit.set! b1 (some downId)).set! b2 (some s.nextNode),
        parent:=if v4 then Slot.root4 else Slot.root6})]
    peers := s.peers.map (appendOwner s.nextNode pid)
    nextNode := s.nextNode+1+1 }

/-- Stage 1, data, NULL parent: two connections under the internal node, then the
internal node published in the root slot of its family. -/
theorem reconstruct_intermediate_root {names : Names} {machine : MachineState}
    {key cidr common pid base base2 downId downBase b1 b2 : Nat}
    {memory initialized : DataMem} {d : Device} (v4 : Bool)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory initialized base2 key common
      machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (bit1 : b1<2) (bit2 : b2<2) :
    reconstruct ((names.allocated base).allocated base2) nodeOffsets
      (connectMemory (connectMemory (connectMemory initialized
          downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1))
          base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2))
          base2 (names.table+rootOffset v4) ((names.table+rootOffset v4) ||| 2))=
      .ok (installedIntermediateRoot v4 downId b1 b2 key cidr common
        machine.data.regs.rbp.toNat pid (target d)) := by
  let n1 := names.allocated base
  let n2 := n1.allocated base2
  let mem1 := connectMemory initialized downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1)
  let mem2 := connectMemory mem1 base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2)
  let after := connectMemory mem2 base2 (n2.table+rootOffset v4) ((n2.table+rootOffset v4) ||| 2)
  have full := reconstruct_fields related
  have arena : Arena n2 := arena_of_valid valid2
  have below := ids_below_counter full.valid
  have leafNamed1 : (names.nextNode,base) ∈ n1.trie.nodes := allocated_node names base
  have leafNamed : (names.nextNode,base) ∈ n2.trie.nodes := List.mem_append_left _ leafNamed1
  have internalNamed : (names.nextNode+1,base2) ∈ n2.trie.nodes := allocated_node n1 base2
  have old {p : Nat×Nat} (member : p ∈ names.trie.nodes) : p ∈ n2.trie.nodes :=
    List.mem_append_left _ (List.mem_append_left _ member)
  have leafInternal : names.nextNode≠names.nextNode+1 := by omega
  have downBelow : downId<names.nextNode := below _ downNamed
  have downInternal : downId≠names.nextNode+1 := by omega
  obtain ⟨writes,frame,notOwned⟩ := init.frame
  have wordsNode {current address : Nat} (named : (current,address) ∈ n1.trie.nodes)
      (offset size : Nat) (within : offset+size≤72) (path : String) :
      word initialized path (address+offset) size=word memory path (address+offset) size :=
    (Trie.word_frame frame path _ _ (fun a inside written =>
      notOwned a written (.inr ⟨_,node_allocation named,inRange_within (total:=72) within inside⟩))).symm
  have wordsTable (offset size : Nat) (within : offset+size≤24) (path : String) :
      word initialized path (names.table+offset) size=word memory path (names.table+offset) size :=
    (Trie.word_frame frame path _ _ (fun a inside written =>
      notOwned a written (.inl (inRange_within (total:=24) within inside)))).symm
  have listsApart : ∀ a, ListWrites n1 a → ¬writes a :=
    fun a written inside => notOwned a inside (owned_of_listWrites written)
  have peerInit {current address : Nat} (named : (current,address) ∈ names.trie.peers) :
      decodePeer n1 nodeOffsets initialized current address=
        decodePeer n1 nodeOffsets memory current address := by
    have peerNamed : (current,address) ∈ n1.trie.peers := named
    apply peer_decoder_congr
    · exact (Trie.word_frame frame "peer.refcount" _ _ (fun a inside written =>
        notOwned a written (.inr ⟨_,peer_allocation peerNamed,
          inRange_within (total:=1520) (by decide) inside⟩))).symm
    · exact (list_read_frame (fuel:=n1.trie.nodes.length+1) frame listsApart (.peer peerNamed)).symm
  have leafCore1 : Trie.decodeNode n1.trie nodeOffsets initialized base=
      .ok (Trie.targetNode (newNode key cidr machine.data.regs.rbp.toNat (some pid))) := by
    rw [←pending.core]
    symm
    apply Trie.decodeNode_congr
    intro offset size field path
    have within := span_within field
    exact (wordsNode leafNamed1 offset size (by omega) path).symm
  have leafCore2 : Trie.decodeNode n2.trie nodeOffsets initialized base=
      .ok (Trie.targetNode (newNode key cidr machine.data.regs.rbp.toNat (some pid))) :=
    (allocated_fields (Trie.decodeNode_fields leafCore1) (address:=base2)).decode
  have leafC1 : Trie.decodeNode n2.trie nodeOffsets mem1 base=
      .ok (Trie.targetNode (newNode key cidr machine.data.regs.rbp.toNat (some pid))) := by
    simpa only [leafInternal,↓reduceIte] using connect_core_any
      (packed:=(base2+(b1+1)*8) ||| b1) arena bit1 (old downNamed) internalNamed leafNamed leafCore2
  have leafC2 := connect_child (memory:=mem1) arena bit2 leafNamed internalNamed leafInternal leafC1
  have leafFinal : decodeNode n2 nodeOffsets after names.nextNode base=
      .ok (names.nextNode,{newNode key cidr machine.data.regs.rbp.toNat (some pid) with
        parent:=.child (names.nextNode+1) b2}) := by
    have step := connect_root_other (packed:=(n2.table+rootOffset v4) ||| 2) arena internalNamed leafNamed
      leafInternal v4 leafC2
    simpa only [Trie.targetNode,newNode] using step
  have internalC1 := connect_core_any (packed:=(base2+(b1+1)*8) ||| b1) arena bit1
    (old downNamed) internalNamed internalNamed init.core
  simp only [↓reduceIte] at internalC1
  have internalC2 := connect_core_any (packed:=(base2+(b2+1)*8) ||| b2) arena bit2
    leafNamed internalNamed internalNamed internalC1
  simp only [↓reduceIte] at internalC2
  have internalC3 := connect_root_child (memory:=mem2) (childId:=names.nextNode+1) arena internalNamed v4
    internalC2
  have internalFinal : decodeNode n2 nodeOffsets after (names.nextNode+1) base2=
      .ok (names.nextNode+1,{newNode key common machine.data.regs.rbp.toNat none with
        bit:=((newNode key common machine.data.regs.rbp.toNat none).bit.set! b1 (some downId)).set! b2
          (some names.nextNode),
        parent:=if v4 then Slot.root4 else Slot.root6}) := by
    simpa only [Trie.targetNode,newNode] using internalC3.1
  have rootPointer (path : String) : Trie.pointer n2.trie.nodes path base2=.ok (some (names.nextNode+1)) :=
    pointer_named arena.addresses internalNamed (arena.positive _ internalNamed) path
  have keepTable (offset) (within : offset+8≤24)
      (different : offset+8≤rootOffset v4 ∨ rootOffset v4+8≤offset) (path) :
      word after path (names.table+offset) 8=word machine.data.dmem path (names.table+offset) 8 :=
    (connect_root_table (n:=n2) arena internalNamed v4 within different path).trans
    ((Trie.word_frame (connect_frame mem1 base _ _) path _ _
      (connect_table_apart valid2 arena.geometry leafNamed internalNamed bit2 within)).symm.trans
    ((Trie.word_frame (connect_frame initialized downBase _ _) path _ _
      (connect_table_apart valid2 arena.geometry (old downNamed) internalNamed bit1 within)).symm.trans
    ((wordsTable offset 8 within path).trans (pending.table offset 8 within path))))
  obtain ⟨root4,root4Read,root4Pointer⟩ := full.root4
  obtain ⟨root6,root6Read,root6Pointer⟩ := full.root6
  let table : AllowedIps := if v4 then {d.peerAllowedips with root4:=some (names.nextNode+1)}
    else {d.peerAllowedips with root6:=some (names.nextNode+1)}
  have newRoot4 : ∃ raw, word after "table.root4" (names.table+AllowedipsMutationLayout.root4) 8=.ok raw ∧
      Trie.pointer n2.trie.nodes "table.root4" raw=.ok table.root4 := by
    cases v4
    · exact ⟨root4,(keepTable 0 (by decide) (.inl (by decide)) "table.root4").trans root4Read,
        pointer_suffix (pointer_suffix root4Pointer)⟩
    · exact ⟨base2,word_path "table.root4" internalC3.2,rootPointer "table.root4"⟩
  have newRoot6 : ∃ raw, word after "table.root6" (names.table+AllowedipsMutationLayout.root6) 8=.ok raw ∧
      Trie.pointer n2.trie.nodes "table.root6" raw=.ok table.root6 := by
    cases v4
    · exact ⟨base2,word_path "table.root6" internalC3.2,rootPointer "table.root6"⟩
    · exact ⟨root6,(keepTable 8 (by decide) (.inr (by decide)) "table.root6").trans root6Read,
        pointer_suffix (pointer_suffix root6Pointer)⟩
  have seqRead : word after "table.seq" (names.table+AllowedipsMutationLayout.seq) 8=.ok table.seq.toNat := by
    have kept := keepTable 16 (by decide) (.inr (by cases v4 <;> decide)) "table.seq"
    cases v4 <;> exact kept.trans full.seq
  have result := reconstruct_allocated_twice (after:=after) (table:=table)
    (connectUpdate downId (names.nextNode+1) b1) (appendOwner names.nextNode pid)
    related valid2 newRoot4 newRoot6 seqRead
    (by
      rintro ⟨current,address⟩ member ⟨actual,node⟩ read
      have identity := (decodeNode_fields read).1
      dsimp only at identity
      subst actual
      have less : current<names.nextNode := below _ member
      have notLeaf : current≠names.nextNode := Nat.ne_of_lt less
      have notInternal : current≠names.nextNode+1 := Nat.ne_of_lt (Nat.lt_succ_of_lt less)
      have r1 := pending.nodes _ member _ read
      have r2 : decodeNode n1 nodeOffsets initialized current address=.ok (current,node) :=
        (record_bytes_congr (fun offset size within path =>
          wordsNode (List.mem_append_left _ member) offset size (by omega) path)).trans r1
      have r3 := decodeNode_allocate (address:=base2) r2
      have c1 := connect_any arena bit1 (old downNamed) internalNamed (old member) downInternal r3
      have c2 : decodeNode n2 nodeOffsets mem2 current address=
          .ok (connectUpdate downId (names.nextNode+1) b1 (current,node)) :=
        (connect_any arena bit2 leafNamed internalNamed (old member) leafInternal c1).trans
          (congrArg Except.ok (connectUpdate_other
            (entry:=connectUpdate downId (names.nextNode+1) b1 (current,node)) notLeaf notInternal))
      exact connect_root_other arena internalNamed (old member) notInternal v4 c2)
    leafFinal internalFinal (by
      rintro ⟨current,address⟩ member value read
      have peerNamed : (current,address) ∈ n2.trie.peers := member
      rw [connect_root_peer arena internalNamed peerNamed v4,
        connect_peer_frame arena.geometry leafNamed internalNamed peerNamed bit2,
        connect_peer_frame arena.geometry (old downNamed) internalNamed peerNamed bit1]
      apply decodePeer_allocate
      rw [peerInit member]
      exact pending.peers _ member _ read)
  have final : reconstruct n2 nodeOffsets after=
      .ok (installedIntermediateRoot v4 downId b1 b2 key cidr common
        machine.data.regs.rbp.toNat pid (target d)) := by
    simpa only [installedIntermediateRoot,←full.nextNode,target,table] using result
  exact final

#print axioms reconstruct_intermediate_root
end Binary.Pair.Allowedips.C1Split
