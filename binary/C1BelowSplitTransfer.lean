import C1BelowSplitPath
import C1BelowSplitHeapMemory
import PairAllowedipsHeapFrame

/- Origin: trial source binary-trials/t5/T5Transfer.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 3 (fifth piece): the machine segment `Add.entry+0x338 .. +0x549`
(non-NULL parent) delivers the data results of stages 1 and 2 at its exit: whatever
reconstruction and `heap` hold on the stage-1 memory hold on the machine's final memory,
which differs from it only in the KCOV callback's footprint. -/
namespace Binary.Pair.Allowedips.C1Split
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.SplitStage3.Path
open Binary.CommonBitsCoverage Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

/-- The memory of stage 1: three connections on the initialized memory. -/
def stage1Memory (m : DataMem) (base base2 downBase parentBase b1 b2 direction : Nat) : DataMem :=
  connectMemory (connectMemory (connectMemory m
      downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1))
      base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2))
      base2 (parentBase+8+direction*8) ((parentBase+(direction+1)*8) ||| direction)

theorem machine_connections_transfer (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte parentIndex parentShift parentByte : Nat)
    {base base2 downBase parentBase : Nat} {n : Names} {S : State}
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
    -- the registers are the interpretation's addresses
    (node : s.regs.r12.toBitVec = .ofNat 64 base2) (down : s.regs.rdi.toBitVec = .ofNat 64 downBase)
    (leaf : s.regs.r8.toBitVec = .ofNat 64 base) (par : s.regs.rbx.toBitVec = .ofNat 64 parentBase)
    -- the callback writes nothing the projection or the structural check reads
    (readApart : ∀ span ∈ readSpans n nodeOffsets, ∀ a, span.contains a → ¬CallWrites s c a)
    (metadataApart : ∀ span ∈ metadataSpans n nodeOffsets, ∀ a, span.contains a → ¬CallWrites s c a)
    (data : reconstruct n nodeOffsets (stage1Memory s.dmem base base2 downBase parentBase b1
      (selected byte shift) (selected parentByte parentShift))=.ok S)
    (shape : heap n S (stage1Memory s.dmem base base2 downBase parentBase b1
      (selected byte shift) (selected parentByte parentShift))=.ok ()) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧
      t.data.regs.rbp = s.regs.rbp ∧ t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
      t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 ∧
      reconstruct n nodeOffsets t.data.dmem=.ok S ∧ heap n S t.data.dmem=.ok () ∧ CallsReady c t.data ∧
      EqualOutside (PathWrites s c b1 (selected byte shift) (selected parentByte parentShift))
        s.dmem t.data.dmem)
      ⟨s, Add.entry + 0x338⟩ := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (connections_nonnull fetch agree tracePc c s b1 byteIndex shift byte parentIndex parentShift parentByte
      entry parent ready contextApart contextApart3 indexRead shiftRead byteRead indexBound shiftBound byteBound
      nodeParentMapped parentLeft parentRight readsApart wordsApart)
  rintro t ⟨mid, frame, pcT, memT, rbxT, rspT, rbpT, r12T, r13T, r14T, r15T, readyT, total⟩
  have framed := (frame.storeInt (s.regs.r12.toBitVec + 48) 8
    (packed s.regs.rbx.toBitVec (selected parentByte parentShift)).toInt).storeInt
    (slot s.regs.rbx.toBitVec (selected parentByte parentShift)) 8 s.regs.r12.toBitVec.toInt
  rw [←memT, node, down, leaf, par, machine_memory_stage1] at framed
  refine ⟨pcT, rbxT, rspT, rbpT, r12T, r13T, r14T, r15T, ?_, ?_, readyT, total⟩
  · rw [←reconstruct_frame n nodeOffsets framed readApart]
    exact data
  · rw [←heap_frame n nodeOffsets S framed metadataApart]
    exact shape

#print axioms machine_connections_transfer
end Binary.Pair.Allowedips.C1Split
