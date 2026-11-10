import C1BelowSplitHeap

/- Origin: trial source binary-trials/t5/T5HeapMemory.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 2 capstone: the structural assertion on the memory after the
internal node's initialization and the six connection stores, from the same
resources the reconstruction lemma uses. -/
namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG Root

theorem owned_of_listWrites {n : Names} {a : BitVec 64} (written : ListWrites n a) : Owned n a := by
  obtain ⟨link,slot,offset,which,inside⟩ := written
  right
  cases slot with
  | node named =>
    exact ⟨_,node_allocation named,inRange_within (offset:=56+offset) (size:=8) (total:=72)
      (by rcases which with rfl|rfl <;> decide) (by simpa only [Nat.add_assoc] using inside)⟩
  | peer named =>
    exact ⟨_,peer_allocation named,inRange_within (offset:=1096+offset) (size:=8) (total:=1520)
      (by rcases which with rfl|rfl <;> decide) (by simpa only [Nat.add_assoc] using inside)⟩

theorem address_allocate {names : Names} {id a address : Nat}
    (found : Trie.address names.trie.nodes (some id)=.ok a) :
    Trie.address (names.allocated address).trie.nodes (some id)=.ok a := by
  unfold Trie.address at found ⊢
  cases lookup : names.trie.nodes.find? (·.1==id) with
  | none => simp [lookup] at found
  | some pair => simpa [Names.allocated,List.find?_append,lookup] using found

theorem internalListCheck_allocate {names : Names} {m : DataMem} {id address : Nat}
    (checked : internalListCheck names m id=.ok ()) :
    internalListCheck (names.allocated address) m id=.ok () := by
  unfold internalListCheck at checked ⊢
  obtain ⟨a,found,rest⟩ := bind_ok checked
  rw [address_allocate found]
  exact rest

#print axioms internalListCheck_allocate

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- A self-linked list head satisfies the internal-node list check. -/
theorem internalListCheck_of_head {n : Names} {m : DataMem} {id a : Nat}
    (found : Trie.address n.trie.nodes (some id)=.ok a)
    (next : readNat ⟨{dmem:=m},0⟩ (a+56) 8=.ok (a+56))
    (previous : readNat ⟨{dmem:=m},0⟩ (a+56+8) 8=.ok (a+56)) :
    internalListCheck n m id=.ok () := by
  simp only [internalListCheck,found,ok_bind,AllowedipsMutationLayout.peer_list,next,previous,
    beq_self_eq_true,Bool.and_self]
  rfl

/-- The three connections leave every list head intact. -/
theorem internal_three_connects {n : Names} {m : DataMem}
    {c1 c1Base p1 p1Base d1 k1 c2 c2Base p2 p2Base d2 k2 c3 c3Base p3 p3Base d3 k3 : Nat}
    (g : Geometry n nodeOffsets)
    (n1c : (c1,c1Base) ∈ n.trie.nodes) (n1p : (p1,p1Base) ∈ n.trie.nodes) (b1 : d1<2)
    (n2c : (c2,c2Base) ∈ n.trie.nodes) (n2p : (p2,p2Base) ∈ n.trie.nodes) (b2 : d2<2)
    (n3c : (c3,c3Base) ∈ n.trie.nodes) (n3p : (p3,p3Base) ∈ n.trie.nodes) (b3 : d3<2)
    (id : Nat) (checked : internalListCheck n m id=.ok ()) :
    internalListCheck n (connectMemory (connectMemory (connectMemory m
      c1Base (p1Base+8+d1*8) k1) c2Base (p2Base+8+d2*8) k2) c3Base (p3Base+8+d3*8) k3) id=.ok () :=
  (internal_list_frame n (connect_frame _ c3Base (p3Base+8+d3*8) k3) (connect_lists_apart g n3c n3p b3) id) ▸
  (internal_list_frame n (connect_frame _ c2Base (p2Base+8+d2*8) k2) (connect_lists_apart g n2c n2p b2) id) ▸
  (internal_list_frame n (connect_frame m c1Base (p1Base+8+d1*8) k1) (connect_lists_apart g n1c n1p b1) id) ▸
  checked

/-- Stage 2: `heap` holds for the reconstructed state on the final memory. -/
theorem intermediate_connect_heap {names : Names} {machine : MachineState}
    {key cidr common pid base base2 downId downBase parentId parentBase b1 b2 direction : Nat}
    {memory initialized : DataMem} {d : Device} {parentNode downNode : AipNode} (owner : Peer)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (checked : heap names (target d) machine.data.dmem=.ok ())
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory initialized base2 key common
      machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (hasPeer : d.peers.get? pid=some owner)
    (parent : (parentId,parentNode) ∈ (target d).nodes) (down : (downId,downNode) ∈ (target d).nodes)
    (bit : direction<2) (bit1 : b1<2) (bit2 : b2<2)
    (occupied : parentNode.bit[direction]?=some (some downId))
    (sameWidth : machine.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<common)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=direction)
    (downMeasure : common<downNode.cidr) (leafMeasure : common<cidr)
    (downPrefix : downNode.bits/2^(machine.data.regs.rbp.toNat-common)=
      key/2^(machine.data.regs.rbp.toNat-common))
    (downSide : downNode.bits/2^(machine.data.regs.rbp.toNat-1-common)%2=b1)
    (leafSide : key/2^(machine.data.regs.rbp.toNat-1-common)%2=b2) (sides : b1≠b2) :
    heap ((names.allocated base).allocated base2)
      (installedIntermediate downId b1 b2 parentId direction key cidr common
        machine.data.regs.rbp.toNat pid (target d))
      (connectMemory (connectMemory (connectMemory initialized
          downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1))
          base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2))
          base2 (parentBase+8+direction*8) ((parentBase+(direction+1)*8) ||| direction))=.ok () := by
  let n1 := names.allocated base
  let n2 := n1.allocated base2
  have full := reconstruct_fields related
  have arena : Arena n2 := arena_of_valid valid2
  have leafNamed : (names.nextNode,base) ∈ n2.trie.nodes :=
    List.mem_append_left _ (allocated_node names base)
  have internalNamed : (names.nextNode+1,base2) ∈ n2.trie.nodes := allocated_node n1 base2
  have old {p : Nat×Nat} (member : p ∈ names.trie.nodes) : p ∈ n2.trie.nodes :=
    List.mem_append_left _ (List.mem_append_left _ member)
  obtain ⟨writes,frame,notOwned⟩ := init.frame
  have listsApart : ∀ a, ListWrites n1 a → ¬writes a :=
    fun a written inside => notOwned a inside (owned_of_listWrites written)
  have connects (id : Nat) (start : internalListCheck n2 initialized id=.ok ()) :=
    internal_three_connects (k1:=(base2+(b1+1)*8) ||| b1) (k2:=(base2+(b2+1)*8) ||| b2)
      (k3:=(parentBase+(direction+1)*8) ||| direction) arena.geometry
      (old downNamed) internalNamed bit1 leafNamed internalNamed bit2
      internalNamed (old parentNamed) bit id start
  apply heap_installedIntermediate owner related checked hasPeer parent down bit bit1 bit2 occupied
    sameWidth measure prefixEq side downMeasure leafMeasure downPrefix downSide leafSide sides
  · intro current node member internal
    apply connects
    apply internalListCheck_allocate
    exact (internal_list_frame n1 frame listsApart current) ▸ pending.internal current node member internal
  · rw [full.nextNode]
    apply connects
    have found : n2.trie.nodes.find? (·.1==names.nextNode+1)=some (names.nextNode+1,base2) :=
      Trie.find_node_key arena.ids internalNamed
    exact internalListCheck_of_head (by simp only [Trie.address,found]; rfl) init.head.1 init.head.2

#print axioms intermediate_connect_heap
end Binary.Pair.Allowedips.C1Split
