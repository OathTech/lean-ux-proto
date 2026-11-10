import C1BelowSplitMain
import AllowedipsReturnFrame

/- Origin: trial source binary-trials/t5/T5Return.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, capstone to the return (non-NULL parent): `Add.entry+0x338` through the
three connections, the common exit's KCOV call and the epilogue (landed
`Return.finish_checked`), to the caller's return address, with the mirror's device and
`heap` at the end. -/
namespace Binary.Pair.Allowedips.C1Split
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.SplitStage3.Path
open Binary.CommonBitsCoverage Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

theorem machine_intermediate_return (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte parentIndex parentShift parentByte : Nat)
    {names : Names} {machine : MachineState} {memory : DataMem} {d : Device}
    {key cidr common pid base base2 downId downBase parentId parentBase : Nat}
    {parentNode downNode : AipNode} (owner : Peer) {regs : Reg64s} {pc : Int64}
    (entry : SplitStage3.Entry s b1 byteIndex shift byte)
    (parent : s.regs.rbx ≠ 0)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a)
    (contextApart3 : ∀ a, c.bytes a → ¬(InRange (s.regs.r12.toBitVec + 48) 8 a ∨
      InRange (slot s.regs.rbx.toBitVec (selected parentByte parentShift)) 8 a))
    (indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 25) 1 = some (parentIndex : Int))
    (shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 26) 1 = some (parentShift : Int))
    (byteRead : s.dmem.loadInt (s.regs.r12.toBitVec + 32 + .ofNat 64 parentIndex) 1 = some (parentByte : Int))
    (indexBound : parentIndex < 16) (shiftBound : parentShift < 8) (byteBound : parentByte < 256)
    (nodeParentMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (parentLeft : (s.dmem.loadInt (s.regs.rbx.toBitVec + 8) 8).isSome = true)
    (parentRight : (s.dmem.loadInt (s.regs.rbx.toBitVec + 16) 8).isSome = true)
    (readsApart : ∀ a, (InRange (s.regs.rbx.toBitVec + 25) 1 a ∨ InRange (s.regs.rbx.toBitVec + 26) 1 a ∨
        InRange (s.regs.r12.toBitVec + 32 + .ofNat 64 parentIndex) 1 a) →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a ∧
      ¬CallWrites s c a)
    (wordsApart : ∀ a, (InRange (s.regs.r12.toBitVec + 48) 8 a ∨ InRange (s.regs.rbx.toBitVec + 8) 8 a ∨
        InRange (s.regs.rbx.toBitVec + 16) 8 a) → ¬CallWrites s c a)
    (node : s.regs.r12.toBitVec = .ofNat 64 base2) (down : s.regs.rdi.toBitVec = .ofNat 64 downBase)
    (leaf : s.regs.r8.toBitVec = .ofNat 64 base) (par : s.regs.rbx.toBitVec = .ofNat 64 parentBase)
    (readApart : ∀ span ∈ readSpans ((names.allocated base).allocated base2) nodeOffsets,
      ∀ a, span.contains a → ¬CallWrites s c a)
    (metadataApart : ∀ span ∈ metadataSpans ((names.allocated base).allocated base2) nodeOffsets,
      ∀ a, span.contains a → ¬CallWrites s c a)
    -- the epilogue's saved words, read in the entry state with the return value 0 in `rbx`,
    -- and their separation from everything the segment writes
    (checked : Return.addEffect {s with regs:={s.regs with rbx:=0}}=.ok (regs,pc))
    (savedApart : ∀ offset ∈ [48,56,64,72,80,88,96], ∀ a,
      InRange (s.regs.rsp.toBitVec+.ofNat 64 offset) 8 a →
      ¬PathWrites s c b1 (selected byte shift) (selected parentByte parentShift) a)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (heapBefore : heap names (target d) machine.data.dmem=.ok ())
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory s.dmem base2 key common machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (hasDown : d.nodes.get? downId=some downNode) (hasParent : d.nodes.get? parentId=some parentNode)
    (hasPeer : d.peers.get? pid=some owner) (different : downId≠parentId)
    (occupied : parentNode.bit[selected parentByte parentShift]?=some (some downId))
    (sameWidth : machine.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<common)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=selected parentByte parentShift)
    (downMeasure : common<downNode.cidr) (leafMeasure : common<cidr)
    (downPrefix : downNode.bits/2^(machine.data.regs.rbp.toNat-common)=
      key/2^(machine.data.regs.rbp.toNat-common))
    (downSide : downNode.bits/2^(machine.data.regs.rbp.toNat-1-common)%2=b1)
    (leafSide : key/2^(machine.data.regs.rbp.toNat-1-common)%2=selected byte shift)
    (sides : b1≠selected byte shift) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = pc ∧ Return.observed t.data.regs = Return.observed regs ∧
      Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem
        (intermediateInstalled d downId b1 (selected byte shift) parentId (selected parentByte parentShift)
          key cidr common machine.data.regs.rbp.toNat pid downNode parentNode owner) ∧
      heap ((names.allocated base).allocated base2)
        (target (intermediateInstalled d downId b1 (selected byte shift) parentId
          (selected parentByte parentShift) key cidr common machine.data.regs.rbp.toNat pid
          downNode parentNode owner)) t.data.dmem=.ok ())
      ⟨s, Add.entry + 0x338⟩ := by
  apply eventually_trans (instructionStep fetch) _ _ _
    (machine_intermediate_nonnull fetch agree tracePc c s b1 byteIndex shift byte parentIndex parentShift
      parentByte owner entry parent ready contextApart contextApart3 indexRead shiftRead byteRead indexBound
      shiftBound byteBound nodeParentMapped parentLeft parentRight readsApart wordsApart node down leaf par
      readApart metadataApart related heapBefore pending valid2 init downNamed parentNamed hasDown hasParent
      hasPeer different occupied sameWidth measure prefixEq side downMeasure leafMeasure downPrefix downSide
      leafSide sides)
  rintro t ⟨pcT, rbxT, rspT, _, _, _, _, _, relatedT, shapeT, readyT, total⟩
  obtain ⟨regs', checked', observed'⟩ := Return.addEffect_frame
    (s:={s with regs:={s.regs with rbx:=0}}) (t:=t.data) rspT rbxT total savedApart checked
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

#print axioms machine_intermediate_return
end Binary.Pair.Allowedips.C1Split
