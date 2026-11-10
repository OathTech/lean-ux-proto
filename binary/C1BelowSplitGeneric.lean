import AllowedipsChildReconstruct

/- Origin: trial source binary-trials/t5/T5Generic.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, generic layer: what the landed one-fresh-object machinery had to be
generalised to for two live fresh objects. Nothing here mentions `names.allocated`
except the two-allocation assembly lemma: the connection lemmas are stated for an
arbitrary validated interpretation and arbitrary named child and parent. -/
namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG Root

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- Facts of a validated interpretation, independent of how it was extended. -/
structure Arena (n : Names) : Prop where
  valid : validate n nodeOffsets=.ok ()
  geometry : Geometry n nodeOffsets
  addresses : (n.trie.nodes.map Prod.snd).Nodup
  ids : (n.trie.nodes.map Prod.fst).Nodup
  positive : ∀ p ∈ n.trie.nodes, 0<p.2
  aligned : ∀ p ∈ n.trie.nodes, p.2%8=0

theorem arena_of_valid {n : Names} (valid : validate n nodeOffsets=.ok ()) : Arena n := by
  have original := valid
  unfold validate at valid
  obtain ⟨_,trieValid,_⟩ := bind_ok valid
  have ranges := trie_validate_ranges trieValid
  have pairs := Trie.validate_pairwise trieValid
  have unique := trieValid
  unfold Trie.validate at unique
  obtain ⟨_,unique⟩ := check_ok _ _ _ _ unique
  obtain ⟨_,unique,_⟩ := bind_ok unique
  have all := forIn_ok
    (P := fun pairs : List (Nat×Nat) => (pairs.map Prod.snd).Nodup ∧ (pairs.map Prod.fst).Nodup)
    (fun pairs _ _ _ run => by
      obtain ⟨checked,run⟩ := check_ok _ _ _ _ run
      have lengths : (pairs.map Prod.fst).eraseDups.length=pairs.length ∧
          (pairs.map Prod.snd).eraseDups.length=pairs.length := by simpa using checked
      exact ⟨(),(Except.ok.inj run).symm,nodup_of_eraseDups_length _ (by simpa using lengths.2),
        nodup_of_eraseDups_length _ (by simpa using lengths.1)⟩) unique
  have nodes := all n.trie.nodes (by simp)
  refine ⟨original,⟨?_,pairs⟩,nodes.1,nodes.2,?_,?_⟩
  · intro span member
    exact Nat.le_of_lt (ranges span member).2
  · intro p member
    exact (ranges (p.2,nodeOffsets.nodeSize) (node_allocation (id:=p.1) member)).1
  · intro p member
    exact validate_node_aligned original (id:=p.1) member

#print axioms arena_of_valid

theorem Arena.address_ne {n : Names} (arena : Arena n) {a b aBase bBase : Nat}
    (first : (a,aBase) ∈ n.trie.nodes) (second : (b,bBase) ∈ n.trie.nodes) (different : a≠b) :
    aBase≠bBase := by
  intro equal
  have left := find_address arena.addresses first
  have right := find_address arena.addresses second
  rw [equal] at left
  exact different (congrArg Prod.fst (Option.some.inj (left.symm.trans right)))

/-- One `connect_node(parent->bit[direction], child)` seen from any named record's
core (the part of a record that does not include its own packed parent). This is
what a pending, not yet connected, fresh record needs. -/
theorem connect_core_any {n : Names} {memory : DataMem}
    {childId childBase parentId parentBase direction current address packed : Nat} {node : Trie.Node}
    (arena : Arena n) (bit : direction<2)
    (childNamed : (childId,childBase) ∈ n.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ n.trie.nodes)
    (named : (current,address) ∈ n.trie.nodes)
    (read : Trie.decodeNode n.trie nodeOffsets memory address=.ok node) :
    Trie.decodeNode n.trie nodeOffsets
      (connectMemory memory childBase (parentBase+8+direction*8) packed) address=
      .ok (if current=parentId then {node with children:=node.children.set! direction (some childId)}
        else node) := by
  have g := arena.geometry
  have extent : address+72≤2^64 := g.bounded _ (node_allocation named)
  have childExtent : childBase+72≤2^64 := g.bounded _ (node_allocation childNamed)
  have parentExtent : parentBase+72≤2^64 := g.bounded _ (node_allocation parentNamed)
  have spans (offset size : Nat) (field : (offset,size) ∈ Trie.nodeSpans nodeOffsets) : offset+size≤48 := by
    simp only [Trie.nodeSpans,nodeOffsets,AllowedipsLayout.peer,AllowedipsLayout.bit,
      AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,
      AllowedipsLayout.bitlen,AllowedipsLayout.bits,List.mem_cons,List.not_mem_nil,
      or_false,Prod.mk.injEq] at field
    omega
  have middle : Trie.decodeNode n.trie nodeOffsets (write64 memory (childBase+48) packed) address=.ok node := by
    rw [←read]
    symm
    apply Trie.decodeNode_congr
    intro offset size field path
    have within := spans offset size field
    symm
    apply word_write64_frame
    exact g.slices_apart (node_allocation named) (node_allocation childNamed)
      offset size 48 8 (by change offset+size≤72; omega) (by dsimp only; decide)
      (fun _ => .inl within)
  unfold connectMemory
  by_cases same : current=parentId
  · subst current
    have equal := Index.unique_first arena.ids named parentNamed
    subst address
    simp only [↓reduceIte]
    exact core_child_write bit (by omega) (by omega) middle
      (fun path => pointer_named arena.addresses childNamed (arena.positive _ childNamed) path)
  · simp only [same,↓reduceIte]
    rw [←middle]
    symm
    apply Trie.decodeNode_congr
    intro offset size field path
    have within := spans offset size field
    symm
    apply word_write64_frame
    rw [Nat.add_assoc]
    exact g.slices_apart (node_allocation named) (node_allocation parentNamed)
      offset size (8+direction*8) 8 (by change offset+size≤72; omega) (by change 8+direction*8+8≤72; omega)
      (fun equal => False.elim (arena.address_ne named parentNamed same (congrArg Prod.fst equal)))

#print axioms connect_core_any

/-- The child's own record after its connection, from its core alone: the packed
parent word is written here for the first time, so no earlier parent is needed. -/
theorem connect_child {n : Names} {memory : DataMem}
    {childId childBase parentId parentBase direction : Nat} {core : Trie.Node}
    (arena : Arena n) (bit : direction<2)
    (childNamed : (childId,childBase) ∈ n.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ n.trie.nodes)
    (different : childId≠parentId)
    (coreRead : Trie.decodeNode n.trie nodeOffsets memory childBase=.ok core) :
    decodeNode n nodeOffsets
      (connectMemory memory childBase (parentBase+8+direction*8) ((parentBase+(direction+1)*8) ||| direction))
      childId childBase=
      .ok (childId,({
        peer:=core.peer,bit:=core.children,cidr:=core.cidr,bitlen:=core.width,
        bits:=core.key,parent:=Slot.child parentId direction} : AipNode)) := by
  have g := arena.geometry
  have childExtent : childBase+72≤2^64 := g.bounded _ (node_allocation childNamed)
  have parentExtent : parentBase+72≤2^64 := g.bounded _ (node_allocation parentNamed)
  have parentPointer : Trie.pointer n.trie.nodes "node.parent" parentBase=.ok (some parentId) :=
    pointer_named arena.addresses parentNamed (arena.positive _ parentNamed) "node.parent"
  have parentRead := parent_child (names:=n) (arena.aligned _ parentNamed) bit parentPointer
  have slotEq : parentBase+8+direction*8=parentBase+(direction+1)*8 := by omega
  rw [slotEq]
  exact (connect_record (names:=n) (id:=childId) (by omega : childBase+56≤2^64)
    (by omega : parentBase+(direction+1)*8+8≤2^64)
    (Nat.or_lt_two_pow (by omega : parentBase+(direction+1)*8<2^64) (by omega : direction<2^64))
    coreRead parentRead (by
      intro a old slotRead
      apply g.slices_apart (node_allocation childNamed) (node_allocation parentNamed)
        0 56 (8+direction*8) 8 (by dsimp only; decide) (by change 8+direction*8+8≤72; omega)
        (fun equal => False.elim (arena.address_ne childNamed parentNamed different (congrArg Prod.fst equal))) a
        (by simpa only [Nat.add_zero] using old)
      have offsetEq : (direction+1)*8=8+direction*8 := by omega
      simpa only [offsetEq] using slotRead)).1

#print axioms connect_child

/-- The record-level effect of one connection on an arbitrary record. -/
def connectUpdate (child parent direction : Nat) (entry : NodeId×AipNode) : NodeId×AipNode :=
  (entry.1,if entry.1=child then {entry.2 with parent:=.child parent direction}
    else if entry.1=parent then {entry.2 with bit:=entry.2.bit.set! direction (some child)} else entry.2)

theorem connectUpdate_other {child parent direction : Nat} {entry : NodeId×AipNode}
    (notChild : entry.1≠child) (notParent : entry.1≠parent) :
    connectUpdate child parent direction entry=entry := by
  simp only [connectUpdate,notChild,notParent,↓reduceIte]

/-- One connection seen from any fully decoded record: child, parent or bystander.
Generic in the interpretation and in which named nodes are child and parent. -/
theorem connect_any {n : Names} {memory : DataMem}
    {childId childBase parentId parentBase direction current address : Nat} {node : AipNode}
    (arena : Arena n) (bit : direction<2)
    (childNamed : (childId,childBase) ∈ n.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ n.trie.nodes)
    (named : (current,address) ∈ n.trie.nodes)
    (different : childId≠parentId)
    (read : decodeNode n nodeOffsets memory current address=.ok (current,node)) :
    decodeNode n nodeOffsets
      (connectMemory memory childBase (parentBase+8+direction*8) ((parentBase+(direction+1)*8) ||| direction))
      current address=
      .ok (connectUpdate childId parentId direction (current,node)) := by
  have g := arena.geometry
  have extent : address+72≤2^64 := g.bounded _ (node_allocation named)
  have childExtent : childBase+72≤2^64 := g.bounded _ (node_allocation childNamed)
  have parentExtent : parentBase+72≤2^64 := g.bounded _ (node_allocation parentNamed)
  unfold decodeNode at read
  obtain ⟨core,coreRead,read⟩ := bind_ok read
  obtain ⟨parentWord,parentRead,read⟩ := bind_ok read
  obtain ⟨slot,slotRead,read⟩ := bind_ok read
  cases Except.ok.inj read
  by_cases isChild : current=childId
  · subst current
    have equal := Index.unique_first arena.ids named childNamed
    subst address
    have result := connect_child (memory:=memory) arena bit childNamed parentNamed different coreRead
    simpa only [connectUpdate,↓reduceIte] using result
  · have coreAfter := connect_core_any
      (packed:=(parentBase+(direction+1)*8) ||| direction) arena bit childNamed parentNamed named coreRead
    have parentAfter : word (connectMemory memory childBase (parentBase+8+direction*8)
        ((parentBase+(direction+1)*8) ||| direction)) "node.parent"
        (address+AllowedipsMutationLayout.parent_bit_packed) 8=.ok parentWord := by
      rw [←parentRead]
      unfold connectMemory
      refine (word_write64_frame _ _ _ _ _ _ ?_).trans (word_write64_frame _ _ _ _ _ _ ?_)
      · rw [Nat.add_assoc]
        exact g.slices_apart (node_allocation named) (node_allocation parentNamed)
          48 8 (8+direction*8) 8 (by dsimp only; decide) (by change 8+direction*8+8≤72; omega)
          (fun _ => .inr (by omega))
      · exact g.slices_apart (node_allocation named) (node_allocation childNamed)
          48 8 48 8 (by dsimp only; decide) (by dsimp only; decide)
          (fun equal => False.elim (arena.address_ne named childNamed isChild (congrArg Prod.fst equal)))
    by_cases isParent : current=parentId
    · subst isParent
      simp only [decodeNode,coreAfter,parentAfter,slotRead,ok_bind,connectUpdate,isChild,↓reduceIte]
      rfl
    · simp only [decodeNode,coreAfter,parentAfter,slotRead,ok_bind,connectUpdate,isChild,isParent,↓reduceIte]
      rfl

#print axioms connect_any

/-- Adding one allocation preserves every decoded peer on the same memory. -/
theorem decodePeer_allocate {names : Names} {m : DataMem} {id base address : Nat}
    {entry : PeerId×Nat×List NodeId}
    (decoded : decodePeer names nodeOffsets m id base=.ok entry) :
    decodePeer (names.allocated address) nodeOffsets m id base=.ok entry := by
  unfold decodePeer at decoded ⊢
  obtain ⟨count,countRead,decoded⟩ := bind_ok decoded
  obtain ⟨first,firstRead,decoded⟩ := bind_ok decoded
  obtain ⟨list,listRead,decoded⟩ := bind_ok decoded
  have grown := Ring.peerList_allocate (address:=address) listRead
  rw [countRead,ok_bind]
  dsimp only
  rw [firstRead,ok_bind,grown,ok_bind]
  exact decoded

#print axioms decodePeer_allocate

/-- Assembly after two physical allocations with no reconstructable state in
between: the first fresh record need not decode until the final memory. The landed
`reconstruct_allocated` cannot be iterated here, because its `entry` premise for the
second extension would be a reconstruction of the pending state, which does not
exist (a pending leaf's packed parent word is zero and `parent names 0` fails). -/
theorem reconstruct_allocated_twice {names o before after state first second firstNode secondNode table}
    (nodeUpdate : NodeId×AipNode → NodeId×AipNode)
    (peerUpdate : PeerId×Nat×List NodeId → PeerId×Nat×List NodeId)
    (entry : reconstruct names o before=.ok state)
    (valid : validate ((names.allocated first).allocated second) o=.ok ())
    (root4 : ∃ raw,word after "table.root4" (names.table+AllowedipsMutationLayout.root4) 8=.ok raw ∧
      Trie.pointer ((names.allocated first).allocated second).trie.nodes "table.root4" raw=.ok table.root4)
    (root6 : ∃ raw,word after "table.root6" (names.table+AllowedipsMutationLayout.root6) 8=.ok raw ∧
      Trie.pointer ((names.allocated first).allocated second).trie.nodes "table.root6" raw=.ok table.root6)
    (seq : word after "table.seq" (names.table+AllowedipsMutationLayout.seq) 8=.ok table.seq.toNat)
    (nodes : ∀ pair ∈ names.trie.nodes, ∀ value,
      decodeNode names o before pair.1 pair.2=.ok value →
      decodeNode ((names.allocated first).allocated second) o after pair.1 pair.2=.ok (nodeUpdate value))
    (freshFirst : decodeNode ((names.allocated first).allocated second) o after names.nextNode first=
      .ok (names.nextNode,firstNode))
    (freshSecond : decodeNode ((names.allocated first).allocated second) o after (names.nextNode+1) second=
      .ok (names.nextNode+1,secondNode))
    (peers : ∀ pair ∈ names.trie.peers, ∀ value,
      decodePeer names o before pair.1 pair.2=.ok value →
      decodePeer ((names.allocated first).allocated second) o after pair.1 pair.2=.ok (peerUpdate value)) :
    reconstruct ((names.allocated first).allocated second) o after=
      .ok ⟨table,state.nodes.map nodeUpdate++[(names.nextNode,firstNode)]++[(names.nextNode+1,secondNode)],
        state.peers.map peerUpdate,names.nextNode+1+1⟩ := by
  unfold reconstruct at entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨oldNodes,nodeReads,entry⟩ := bind_ok entry
  obtain ⟨oldPeers,peerReads,entry⟩ := bind_ok entry
  cases Except.ok.inj entry
  have ns := mapM_update nodeUpdate nodeReads nodes
  have ps := mapM_update peerUpdate peerReads peers
  obtain ⟨r4,r4Read,r4Decode⟩ := root4
  obtain ⟨r6,r6Read,r6Decode⟩ := root6
  have tableEq : ((names.allocated first).allocated second).table=names.table := rfl
  simp only [reconstruct,valid,ok_bind,tableEq,r4Read,r4Decode,r6Read,r6Decode,seq,Nat.toUInt64,UInt64.ofNat_toNat]
  change (do
    let nodes ← ((names.trie.nodes++[(names.nextNode,first)])++[(names.nextNode+1,second)]).mapM
      (fun (id,base) => decodeNode ((names.allocated first).allocated second) o after id base)
    let peers ← names.trie.peers.mapM
      (fun (id,base) => decodePeer ((names.allocated first).allocated second) o after id base)
    pure ({table,nodes,peers,nextNode:=names.nextNode+1+1} : State))=_
  rw [List.mapM_append,List.mapM_append,ns,ps]
  simp only [List.mapM_cons,List.mapM_nil,freshFirst,freshSecond,ok_bind]
  rfl

#print axioms reconstruct_allocated_twice
end Binary.Pair.Allowedips.C1Split
