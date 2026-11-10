import C1BelowSplitRootHeapMemory
import AllowedipsReturnFrame

/- Origin: trial source binary-trials/t5/T5RootReturn.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, capstone to the return, NULL-parent subcase: `Add.entry+0x338` through
two connections, the root publication, the exit's KCOV call and the epilogue (landed
`Return.finish_checked`), with the mirror's device and `heap` at the end. -/
namespace Binary.Pair.Allowedips.C1Split
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.SplitStage3.Path
open Binary.CommonBitsCoverage Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

theorem machine_intermediate_root_return (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte : Nat) (v4 : Bool)
    {names : Names} {machine : MachineState} {memory : DataMem} {d : Device}
    {key cidr common pid base base2 downId downBase : Nat} {downNode : AipNode} (owner : Peer)
    {regs : Reg64s} {pc : Int64}
    (entry : SplitStage3.Entry s b1 byteIndex shift byte)
    (noParent : s.regs.rbx = 0)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a)
    (contextApartRoot : ∀ a, c.bytes a → ¬(InRange (s.regs.r12.toBitVec + 48) 8 a ∨
      InRange (BitVec.ofNat 64 (names.table+rootOffset v4)) 8 a))
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 =
      some (BitVec.ofNat 64 (names.table+rootOffset v4)).toInt)
    (nodeParentMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (rootMapped : (s.dmem.loadInt (BitVec.ofNat 64 (names.table+rootOffset v4)) 8).isSome = true)
    (savedSlotApart : ∀ a, InRange (s.regs.rsp.toBitVec + 8) 8 a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a ∧
      ¬CallWrites s c a)
    (wordsApart : ∀ a, (InRange (s.regs.r12.toBitVec + 48) 8 a ∨
      InRange (BitVec.ofNat 64 (names.table+rootOffset v4)) 8 a) → ¬CallWrites s c a)
    (node : s.regs.r12.toBitVec = .ofNat 64 base2) (down : s.regs.rdi.toBitVec = .ofNat 64 downBase)
    (leaf : s.regs.r8.toBitVec = .ofNat 64 base)
    (readApart : ∀ span ∈ readSpans ((names.allocated base).allocated base2) nodeOffsets,
      ∀ a, span.contains a → ¬CallWrites s c a)
    (metadataApart : ∀ span ∈ metadataSpans ((names.allocated base).allocated base2) nodeOffsets,
      ∀ a, span.contains a → ¬CallWrites s c a)
    (checked : Return.addEffect s=.ok (regs,pc))
    (savedApart : ∀ offset ∈ [48,56,64,72,80,88,96], ∀ a,
      InRange (s.regs.rsp.toBitVec+.ofNat 64 offset) 8 a →
      ¬RootPathWrites s c b1 (selected byte shift) (BitVec.ofNat 64 (names.table+rootOffset v4)) a)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (heapBefore : heap names (target d) machine.data.dmem=.ok ())
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory s.dmem base2 key common machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (hasDown : d.nodes.get? downId=some downNode) (hasPeer : d.peers.get? pid=some owner)
    (rootHere : (if v4 then (target d).table.root4 else (target d).table.root6)=some downId)
    (otherRoot : (if v4 then (target d).table.root6 else (target d).table.root4)≠some downId)
    (family : machine.data.regs.rbp.toNat=if v4 then 32 else 128)
    (downWidth : downNode.bitlen=machine.data.regs.rbp.toNat)
    (downMeasure : common<downNode.cidr) (leafMeasure : common<cidr)
    (downPrefix : downNode.bits/2^(machine.data.regs.rbp.toNat-common)=
      key/2^(machine.data.regs.rbp.toNat-common))
    (downSide : downNode.bits/2^(machine.data.regs.rbp.toNat-1-common)%2=b1)
    (leafSide : key/2^(machine.data.regs.rbp.toNat-1-common)%2=selected byte shift)
    (sides : b1≠selected byte shift) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = pc ∧ Return.observed t.data.regs = Return.observed regs ∧
      Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem
        (intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
          machine.data.regs.rbp.toNat pid downNode owner) ∧
      heap ((names.allocated base).allocated base2)
        (target (intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
          machine.data.regs.rbp.toNat pid downNode owner)) t.data.dmem=.ok ())
      ⟨s, Add.entry + 0x338⟩ := by
  have bit1 := entry.directionBound
  have bit2 := Direct.selected_bound byte shift
  apply eventually_trans (instructionStep fetch) _ _ _
    (connections_root fetch agree tracePc c s b1 byteIndex shift byte _ entry noParent ready contextApart
      contextApartRoot slotRead nodeParentMapped rootMapped savedSlotApart wordsApart)
  rintro t ⟨mid, frame, pcT, memT, rbxT, rspT, _, _, _, _, _, readyT, total⟩
  have framed := (frame.storeInt (s.regs.r12.toBitVec + 48) 8
    (BitVec.ofNat 64 (names.table+rootOffset v4) ||| 2).toInt).storeInt
    (BitVec.ofNat 64 (names.table+rootOffset v4)) 8 s.regs.r12.toBitVec.toInt
  rw [←memT, node, down, leaf, memRoot_connectMemory, connected_connectMemory] at framed
  have targetEq := target_intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
    machine.data.regs.rbp.toNat pid downNode owner hasDown hasPeer (target_nodes_below related)
  have relatedT : Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem
      (intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
        machine.data.regs.rbp.toNat pid downNode owner) := by
    have data := intermediate_root_corresponds (downNode:=downNode) (owner:=owner) v4 related pending valid2
      init downNamed bit1 bit2 hasDown hasPeer
    unfold Corresponds at data ⊢
    rw [←reconstruct_frame _ nodeOffsets framed readApart]
    exact data
  have shapeT : heap ((names.allocated base).allocated base2)
      (target (intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
        machine.data.regs.rbp.toNat pid downNode owner)) t.data.dmem=.ok () := by
    rw [targetEq,←heap_frame _ nodeOffsets _ framed metadataApart]
    exact intermediate_root_heap owner v4 related heapBefore pending valid2 init downNamed hasPeer
      (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown) bit1 bit2 rootHere otherRoot family
      downWidth downMeasure leafMeasure downPrefix downSide leafSide sides
  obtain ⟨regs', checked', observed'⟩ := Return.addEffect_frame (s:=s) (t:=t.data) rspT
    (rbxT.trans noParent.symm) total savedApart checked
  rw [Placement.at_pc t _ pcT]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Return.finish_checked fetch agree tracePc c readyT checked'
      (by
        intro offset member a inside written
        unfold Return.Writes at written
        rw [rspT] at inside written
        exact savedApart offset member a inside (.inr (.inl written)))
      relatedT shapeT
      (by
        intro span member a contained written
        unfold Return.Writes at written
        rw [rspT] at written
        exact readApart span member a contained written))
  rintro r ⟨pcR, observedR, _, _, relatedR, shapeR⟩
  exact ⟨pcR, observedR.trans observed', relatedR, shapeR⟩

#print axioms machine_intermediate_root_return
end Binary.Pair.Allowedips.C1Split
