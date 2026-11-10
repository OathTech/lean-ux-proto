import C1BelowSplitFacts

/-! Result C1, work package 3, the split path: two of the three machine-selected
bits of T5's capstones, derived (T5 assumed them as `leafSide` and `side`).
Both read selector bytes of one node and a stored key byte of another in the
memory after the internal node's initialization; `InternalInit.frame` carries
the pending decodes there. The third bit (`b1`, for the node below) is
computed by the `choose` before `Add.entry+0x338` and is not treated here. -/
namespace Binary.Pair.Allowedips.C1Split
open AllowedipsChild Binary.SplitStage3 Leanux Leanux.WG Root Binary.Statements.C1.Proof

/-- A node named by the interpretation that names the pending leaf decodes
after the internal node's initialization as it did before. -/
theorem InternalInit.keeps_node {names1 : Names} {memory initialized : DataMem}
    {base2 key common width current address : Nat} {node : Trie.Node}
    (init : InternalInit names1 memory initialized base2 key common width)
    (named : (current,address) ∈ names1.trie.nodes)
    (decoded : Trie.decodeNode names1.trie nodeOffsets memory address=.ok node) :
    Trie.decodeNode names1.trie nodeOffsets initialized address=.ok node := by
  obtain ⟨writes,frame,notOwned⟩ := init.frame
  rw [←decoded]
  apply Eq.symm
  apply Trie.decodeNode_congr
  intro offset size field path
  have within := span_within field
  exact Trie.word_frame frame path _ _ (fun a inside written =>
    notOwned a written (.inr ⟨_,node_allocation named,inRange_within (total:=72) (by omega) inside⟩))

/-- T5's `leafSide`: the bit selected for the new leaf under the internal node. -/
theorem split_leaf_bit {names : Names} {before : MachineData} {s : MachineData} {memory : DataMem}
    {d : Device} {key cidr common pid base base2 b1 byteIndex shift byte : Nat}
    (pending : NodeInit.Pending names before d key cidr pid base memory)
    (init : InternalInit (names.allocated base) memory s.dmem base2 key common before.regs.rbp.toNat)
    (entry : SplitStage3.Entry s b1 byteIndex shift byte)
    (node : s.regs.r12.toBitVec = .ofNat 64 base2) (leaf : s.regs.r8.toBitVec = .ofNat 64 base)
    (proper : common<before.regs.rbp.toNat) :
    selected byte shift=key/2^(before.regs.rbp.toNat-1-common)%2 := by
  have leafDecoded := init.keeps_node (allocated_node names base) pending.core
  have indexRead := entry.indexRead
  have shiftRead := entry.shiftRead
  have byteRead := entry.byteRead
  rw [node] at indexRead shiftRead
  rw [leaf] at byteRead
  exact selected_link (sel:=Trie.targetNode (newNode key common before.regs.rbp.toNat none))
    (keyNode:=Trie.targetNode (newNode key cidr before.regs.rbp.toNat (some pid)))
    init.core leafDecoded rfl proper indexRead shiftRead byteRead

/-- T5's `side`: the bit selected for the internal node under the parent. -/
theorem split_parent_bit {names : Names} {before : MachineData} {s : MachineData} {memory : DataMem}
    {d : Device} {key cidr common pid base base2 parentId parentBase parentIndex parentShift parentByte : Nat}
    {parentNode : AipNode}
    (related : Corresponds names nodeOffsets before.dmem d)
    (pending : NodeInit.Pending names before d key cidr pid base memory)
    (init : InternalInit (names.allocated base) memory s.dmem base2 key common before.regs.rbp.toNat)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (hasParent : d.nodes.get? parentId=some parentNode)
    (sameWidth : before.regs.rbp.toNat=parentNode.bitlen) (short : parentNode.cidr<parentNode.bitlen)
    (node : s.regs.r12.toBitVec = .ofNat 64 base2) (par : s.regs.rbx.toBitVec = .ofNat 64 parentBase)
    (indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 25) 1 = some (parentIndex : Int))
    (shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 26) 1 = some (parentShift : Int))
    (byteRead : s.dmem.loadInt (s.regs.r12.toBitVec + 32 + .ofNat 64 parentIndex) 1 = some (parentByte : Int)) :
    selected parentByte parentShift=key/2^(parentNode.bitlen-1-parentNode.cidr)%2 := by
  have parentDecoded := init.keeps_node (List.mem_append_left _ parentNamed)
    (pending.old_node related parentNamed hasParent)
  rw [par] at indexRead shiftRead
  rw [node] at byteRead
  exact selected_link (sel:=Trie.targetNode parentNode)
    (keyNode:=Trie.targetNode (newNode key common before.regs.rbp.toNat none))
    parentDecoded init.core sameWidth short indexRead shiftRead byteRead

#print axioms split_leaf_bit
#print axioms split_parent_bit
end Binary.Pair.Allowedips.C1Split
