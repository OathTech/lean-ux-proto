import C1BelowSplitGeneric

/- Origin: trial source binary-trials/t5/T5Reconstruct.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 1 (data): reconstruction after the intermediate-node insertion
of `add()` (allowedips.c:234-248, non-NULL parent): two fresh objects, three
connections, names extended twice. -/
namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG Root

/-- Bytes the interpretation owns: the table and every named allocation. -/
def Owned (n : Names) (a : BitVec 64) : Prop :=
  InRange (.ofNat 64 n.table) 24 a ∨
    ∃ span ∈ allocations n nodeOffsets, InRange (.ofNat 64 span.1) span.2 a

theorem inRange_within {base offset size total : Nat} {a : BitVec 64} (within : offset+size≤total)
    (inside : InRange (.ofNat 64 (base+offset)) size a) : InRange (.ofNat 64 base) total a := by
  obtain ⟨i,bound,equal⟩ := inside
  refine ⟨offset+i,by omega,?_⟩
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal

theorem span_within {offset size : Nat} (field : (offset,size) ∈ Trie.nodeSpans nodeOffsets) :
    offset+size≤48 := by
  simp only [Trie.nodeSpans,nodeOffsets,AllowedipsLayout.peer,AllowedipsLayout.bit,
    AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,
    AllowedipsLayout.bitlen,AllowedipsLayout.bits,List.mem_cons,List.not_mem_nil,
    or_false,Prod.mk.injEq] at field
  omega

/-- Derived resources after the internal node's initialization stores
(`INIT_LIST_HEAD`, `copy_and_assign_cidr`) on the second fresh zeroed object, before
any connection. The analogue of `NodeInit.Pending` for a peerless node; to be
produced by the machine side, not an environmental premise. `names1` is the
interpretation that already names the pending leaf. -/
structure InternalInit (names1 : Names) (memory initialized : DataMem)
    (base2 key common width : Nat) : Prop where
  core : Trie.decodeNode (names1.allocated base2).trie nodeOffsets initialized base2=
    .ok (Trie.targetNode (newNode key common width none))
  head : readNat ⟨{dmem:=initialized},0⟩ (base2+56) 8=.ok (base2+56) ∧
    readNat ⟨{dmem:=initialized},0⟩ (base2+56+8) 8=.ok (base2+56)
  frame : ∃ writes : BitVec 64 → Prop, EqualOutside writes memory initialized ∧
    ∀ a, writes a → ¬Owned names1 a

def installedIntermediate (downId b1 b2 parentId direction key cidr common width pid : Nat)
    (s : State) : State :=
  { s with
    nodes := s.nodes.map (fun e =>
        connectUpdate (s.nextNode+1) parentId direction (connectUpdate downId (s.nextNode+1) b1 e))++
      [(s.nextNode,{newNode key cidr width (some pid) with parent:=.child (s.nextNode+1) b2})]++
      [(s.nextNode+1,{newNode key common width none with
        bit:=((newNode key common width none).bit.set! b1 (some downId)).set! b2 (some s.nextNode),
        parent:=.child parentId direction})]
    peers := s.peers.map (appendOwner s.nextNode pid)
    nextNode := s.nextNode+1+1 }

/-- Stage 1, data: the three connections of the intermediate insertion complete the
reconstruction under the twice-extended names, from one pending leaf (as landed) and
an initialized second fresh object. -/
theorem reconstruct_intermediate_connect {names : Names} {machine : MachineState}
    {key cidr common pid base base2 downId downBase parentId parentBase b1 b2 direction : Nat}
    {memory initialized : DataMem} {d : Device}
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    -- allocator contract for the second `kmem_cache_zalloc`, one extension later
    (valid2 : validate ((names.allocated base).allocated base2) nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory initialized base2 key common
      machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (bit1 : b1<2) (bit2 : b2<2) (bit : direction<2) :
    reconstruct ((names.allocated base).allocated base2) nodeOffsets
      (connectMemory (connectMemory (connectMemory initialized
          downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1))
          base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2))
          base2 (parentBase+8+direction*8) ((parentBase+(direction+1)*8) ||| direction))=
      .ok (installedIntermediate downId b1 b2 parentId direction key cidr common
        machine.data.regs.rbp.toNat pid (target d)) := by
  let n1 := names.allocated base
  let n2 := n1.allocated base2
  let mem1 := connectMemory initialized downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1)
  let mem2 := connectMemory mem1 base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2)
  let after := connectMemory mem2 base2 (parentBase+8+direction*8) ((parentBase+(direction+1)*8) ||| direction)
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
  have parentBelow : parentId<names.nextNode := below _ parentNamed
  have downInternal : downId≠names.nextNode+1 := by omega
  have internalParent : names.nextNode+1≠parentId := by omega
  have leafParent : names.nextNode≠parentId := by omega
  obtain ⟨writes,frame,notOwned⟩ := init.frame
  -- the initialization frame, read at the bytes the first interpretation owns
  have wordsNode {current address : Nat} (named : (current,address) ∈ n1.trie.nodes)
      (offset size : Nat) (within : offset+size≤72) (path : String) :
      word initialized path (address+offset) size=word memory path (address+offset) size :=
    (Trie.word_frame frame path _ _ (fun a inside written =>
      notOwned a written (.inr ⟨_,node_allocation named,inRange_within (total:=72) within inside⟩))).symm
  have wordsTable (offset size : Nat) (within : offset+size≤24) (path : String) :
      word initialized path (names.table+offset) size=word memory path (names.table+offset) size :=
    (Trie.word_frame frame path _ _ (fun a inside written =>
      notOwned a written (.inl (inRange_within (total:=24) within inside)))).symm
  have listsApart : ∀ a, ListWrites n1 a → ¬writes a := by
    rintro a ⟨link,slot,offset,which,inside⟩ written
    apply notOwned a written
    right
    cases slot with
    | node named =>
      exact ⟨_,node_allocation named,inRange_within (offset:=56+offset) (size:=8) (total:=72)
        (by rcases which with rfl|rfl <;> decide) (by simpa only [Nat.add_assoc] using inside)⟩
    | peer named =>
      exact ⟨_,peer_allocation named,inRange_within (offset:=1096+offset) (size:=8) (total:=1520)
        (by rcases which with rfl|rfl <;> decide) (by simpa only [Nat.add_assoc] using inside)⟩
  have peerInit {current address : Nat} (named : (current,address) ∈ names.trie.peers) :
      decodePeer n1 nodeOffsets initialized current address=
        decodePeer n1 nodeOffsets memory current address := by
    have peerNamed : (current,address) ∈ n1.trie.peers := named
    apply peer_decoder_congr
    · exact (Trie.word_frame frame "peer.refcount" _ _ (fun a inside written =>
        notOwned a written (.inr ⟨_,peer_allocation peerNamed,
          inRange_within (total:=1520) (by decide) inside⟩))).symm
    · exact (list_read_frame (fuel:=n1.trie.nodes.length+1) frame listsApart (.peer peerNamed)).symm
  -- the pending leaf
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
    have step := (connect_any arena bit internalNamed (old parentNamed) leafNamed internalParent leafC2).trans
      (congrArg Except.ok (connectUpdate_other leafInternal leafParent))
    simpa only [Trie.targetNode,newNode] using step
  -- the internal node
  have internalC1 := connect_core_any (packed:=(base2+(b1+1)*8) ||| b1) arena bit1
    (old downNamed) internalNamed internalNamed init.core
  simp only [↓reduceIte] at internalC1
  have internalC2 := connect_core_any (packed:=(base2+(b2+1)*8) ||| b2) arena bit2
    leafNamed internalNamed internalNamed internalC1
  simp only [↓reduceIte] at internalC2
  have internalC3 := connect_child (memory:=mem2) arena bit internalNamed (old parentNamed)
    internalParent internalC2
  have internalFinal : decodeNode n2 nodeOffsets after (names.nextNode+1) base2=
      .ok (names.nextNode+1,{newNode key common machine.data.regs.rbp.toNat none with
        bit:=((newNode key common machine.data.regs.rbp.toNat none).bit.set! b1 (some downId)).set! b2
          (some names.nextNode),
        parent:=.child parentId direction}) := by
    simpa only [Trie.targetNode,newNode] using internalC3
  -- the table
  have keepTable (offset size) (within : offset+size≤24) (path) :
      word after path (names.table+offset) size=word machine.data.dmem path (names.table+offset) size :=
    (Trie.word_frame (connect_frame mem2 base2 _ _) path _ _
      (connect_table_apart valid2 arena.geometry internalNamed (old parentNamed) bit within)).symm.trans
    ((Trie.word_frame (connect_frame mem1 base _ _) path _ _
      (connect_table_apart valid2 arena.geometry leafNamed internalNamed bit2 within)).symm.trans
    ((Trie.word_frame (connect_frame initialized downBase _ _) path _ _
      (connect_table_apart valid2 arena.geometry (old downNamed) internalNamed bit1 within)).symm.trans
    ((wordsTable offset size within path).trans (pending.table offset size within path))))
  obtain ⟨root4,root4Read,root4Pointer⟩ := full.root4
  obtain ⟨root6,root6Read,root6Pointer⟩ := full.root6
  have result := reconstruct_allocated_twice (after:=after) (table:=d.peerAllowedips)
    (fun e => connectUpdate (names.nextNode+1) parentId direction
      (connectUpdate downId (names.nextNode+1) b1 e))
    (appendOwner names.nextNode pid)
    related valid2
    ⟨root4,(keepTable 0 8 (by decide) "table.root4").trans root4Read,
      pointer_suffix (pointer_suffix root4Pointer)⟩
    ⟨root6,(keepTable 8 8 (by decide) "table.root6").trans root6Read,
      pointer_suffix (pointer_suffix root6Pointer)⟩
    ((keepTable 16 8 (by decide) "table.seq").trans full.seq)
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
      exact connect_any arena bit internalNamed (old parentNamed) (old member) internalParent c2)
    leafFinal internalFinal (by
      rintro ⟨current,address⟩ member value read
      have peerNamed : (current,address) ∈ n2.trie.peers := member
      rw [connect_peer_frame arena.geometry internalNamed (old parentNamed) peerNamed bit,
        connect_peer_frame arena.geometry leafNamed internalNamed peerNamed bit2,
        connect_peer_frame arena.geometry (old downNamed) internalNamed peerNamed bit1]
      apply decodePeer_allocate
      rw [peerInit member]
      exact pending.peers _ member _ read)
  simpa only [installedIntermediate,←full.nextNode,target] using result

#print axioms reconstruct_intermediate_connect
end Binary.Pair.Allowedips.C1Split
