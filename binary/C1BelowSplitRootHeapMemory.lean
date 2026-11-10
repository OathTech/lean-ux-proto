import C1BelowSplitRootHeap

/- Origin: trial source binary-trials/t5/T5RootHeapMemory.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 2 capstone, NULL-parent subcase: `heap` on the memory after the
internal node's initialization, two connections and the root publication. -/
namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG Root

theorem root_lists_apart {n : Names} {childId childBase : Nat} (arena : Arena n)
    (childNamed : (childId,childBase) ∈ n.trie.nodes) (v4 : Bool) :
    ∀ a, ListWrites n a → ¬ConnectWrites childBase (n.table+rootOffset v4) a := by
  intro a list written
  rcases written with fresh|slot
  · exact node_before_list_apart arena.geometry rfl childNamed (offset:=48) (size:=8) (by decide) a fresh list
  · obtain ⟨span,member,inSpan⟩ := listWrites_allocation list
    exact span_root_apart arena member v4 a inSpan slot

theorem intermediate_root_heap {names : Names} {machine : MachineState}
    {key cidr common pid base base2 downId downBase b1 b2 : Nat}
    {memory initialized : DataMem} {d : Device} {downNode : AipNode} (owner : Peer) (v4 : Bool)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (checked : heap names (target d) machine.data.dmem=.ok ())
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory initialized base2 key common
      machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (hasPeer : d.peers.get? pid=some owner)
    (down : (downId,downNode) ∈ (target d).nodes)
    (bit1 : b1<2) (bit2 : b2<2)
    (rootHere : (if v4 then (target d).table.root4 else (target d).table.root6)=some downId)
    (otherRoot : (if v4 then (target d).table.root6 else (target d).table.root4)≠some downId)
    (family : machine.data.regs.rbp.toNat=if v4 then 32 else 128)
    (downWidth : downNode.bitlen=machine.data.regs.rbp.toNat)
    (downMeasure : common<downNode.cidr) (leafMeasure : common<cidr)
    (downPrefix : downNode.bits/2^(machine.data.regs.rbp.toNat-common)=
      key/2^(machine.data.regs.rbp.toNat-common))
    (downSide : downNode.bits/2^(machine.data.regs.rbp.toNat-1-common)%2=b1)
    (leafSide : key/2^(machine.data.regs.rbp.toNat-1-common)%2=b2) (sides : b1≠b2) :
    heap ((names.allocated base).allocated base2)
      (installedIntermediateRoot v4 downId b1 b2 key cidr common machine.data.regs.rbp.toNat pid (target d))
      (connectMemory (connectMemory (connectMemory initialized
          downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1))
          base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2))
          base2 (names.table+rootOffset v4) ((names.table+rootOffset v4) ||| 2))=.ok () := by
  let n1 := names.allocated base
  let n2 := n1.allocated base2
  let mem1 := connectMemory initialized downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1)
  let mem2 := connectMemory mem1 base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2)
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
  have connects (id : Nat) (start : internalListCheck n2 initialized id=.ok ()) :
      internalListCheck n2 (connectMemory mem2 base2 (n2.table+rootOffset v4)
        ((n2.table+rootOffset v4) ||| 2)) id=.ok () :=
    (internal_list_frame n2 (connect_frame mem2 base2 _ _)
      (root_lists_apart arena internalNamed v4) id).symm.trans
    ((internal_list_frame n2 (connect_frame mem1 base _ _)
      (connect_lists_apart arena.geometry leafNamed internalNamed bit2) id).symm.trans
    ((internal_list_frame n2 (connect_frame initialized downBase _ _)
      (connect_lists_apart arena.geometry (old downNamed) internalNamed bit1) id).symm.trans start))
  apply heap_installedIntermediateRoot v4 owner related checked hasPeer down bit1 bit2 rootHere otherRoot
    family downWidth downMeasure leafMeasure downPrefix downSide leafSide sides
  · intro current node member internal
    apply connects
    apply internalListCheck_allocate
    exact (internal_list_frame n1 frame listsApart current) ▸ pending.internal current node member internal
  · rw [full.nextNode]
    apply connects
    have found : n2.trie.nodes.find? (·.1==names.nextNode+1)=some (names.nextNode+1,base2) :=
      Trie.find_node_key arena.ids internalNamed
    exact internalListCheck_of_head (by simp only [Trie.address,found]; rfl) init.head.1 init.head.2

#print axioms intermediate_root_heap
end Binary.Pair.Allowedips.C1Split
