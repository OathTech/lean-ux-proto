import C1BelowSplitMachine
import AllowedipsChildEntryCall

/- Origin: trial source binary-trials/t5/T5Path.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 3 (fourth piece): the image from `Add.entry+0x338` to the common
exit `+0x549` on the non-NULL-parent path: t1's 22 instructions, the KCOV callback at
`+0x38c` (landed `Services.call`), and the third connection (`Third.third_connect`). -/
namespace Binary.SplitStage3.Path
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-- t1's four stores leave everything else alone. -/
theorem connected_frame (m : DataMem) (node down newnode : BitVec 64) (direction bit : Nat) :
    EqualOutside (Writes node down newnode direction bit) m (connected m node down newnode direction bit) := by
  intro a outside
  unfold connected
  exact (((storeInt_frame _ _ _ _ a (fun h => outside (.inl h))).trans
    (storeInt_frame _ _ _ _ a (fun h => outside (.inr (.inl h))))).trans
    (storeInt_frame _ _ _ _ a (fun h => outside (.inr (.inr (.inl h)))))).trans
    (storeInt_frame _ _ _ _ a (fun h => outside (.inr (.inr (.inr h)))))

theorem connected_mapped (m : DataMem) (node down newnode : BitVec 64) (direction bit : Nat) :
    Pair.MappedLe m (connected m node down newnode direction bit) :=
  fun _ _ h => storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _
    (storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ h)))

/-- What the KCOV callback at `+0x38c` may write: its return address slot and the
coverage buffer. -/
def CallWrites (s : MachineData) (c : Context) (a : BitVec 64) : Prop :=
  InRange (s.regs.rsp.toBitVec-8) 8 a ∨ c.writes a

/-- Everything the segment may write. -/
def PathWrites (s : MachineData) (c : Context) (direction bit bit3 : Nat) (a : BitVec 64) : Prop :=
  Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec direction bit a ∨ CallWrites s c a ∨
    InRange (s.regs.r12.toBitVec + 48) 8 a ∨ InRange (slot s.regs.rbx.toBitVec bit3) 8 a

theorem connections_nonnull (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (direction byteIndex shift byte parentIndex parentShift parentByte : Nat)
    (entry : SplitStage3.Entry s direction byteIndex shift byte)
    (parent : s.regs.rbx ≠ 0)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec direction (selected byte shift) a)
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
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec direction (selected byte shift) a ∧
      ¬CallWrites s c a)
    (wordsApart : ∀ a, (InRange (s.regs.r12.toBitVec + 48) 8 a ∨ InRange (s.regs.rbx.toBitVec + 8) 8 a ∨
        InRange (s.regs.rbx.toBitVec + 16) 8 a) → ¬CallWrites s c a) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t => ∃ mid : DataMem,
      EqualOutside (CallWrites s c)
        (connected s.dmem s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec direction
          (selected byte shift)) mid ∧
      t.pc = Add.entry + 0x549 ∧
      t.data.dmem = (mid.storeInt (s.regs.r12.toBitVec + 48) 8
          (packed s.regs.rbx.toBitVec (selected parentByte parentShift)).toInt).storeInt
          (slot s.regs.rbx.toBitVec (selected parentByte parentShift)) 8 s.regs.r12.toBitVec.toInt ∧
      t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧ t.data.regs.rbp = s.regs.rbp ∧
      t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧ t.data.regs.r14 = s.regs.r14 ∧
      t.data.regs.r15 = s.regs.r15 ∧ CallsReady c t.data ∧
      EqualOutside (PathWrites s c direction (selected byte shift) (selected parentByte parentShift))
        s.dmem t.data.dmem) ⟨s, Add.entry + 0x338⟩ := by
  have first := Direct.target fetch agree s direction byteIndex shift byte entry
  apply eventually_trans (instructionStep fetch) _ _ _ first
  intro u exit
  obtain ⟨pcU, memU, _, _, _, rbxU, rspU, rbpU, _, _, r12U, r13U, r14U, r15U⟩ := exit
  simp only [parent, ↓reduceIte] at pcU
  have frameU := connected_frame s.dmem s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec
    direction (selected byte shift)
  rw [←memU] at frameU
  have readyU : CallsReady c u.data := ready.frame rspU frameU
    (memU ▸ connected_mapped s.dmem _ _ _ _ _) contextApart
  have here := agree.add _ _ (show Add.fetch (Add.entry+0x38c)=some _ from rfl)
  rw [Binary.Pair.Allowedips.Placement.at_pc u _ pcU]
  apply eventually_trans (instructionStep fetch) _ _ _
    (Binary.Pair.Services.call fetch (Add.entry+0x38c) "L_ffffffff810f31f0" .pc tracePc here c u.data readyU)
  rintro v ⟨pcV, rspV, rbxV, rbpV, r12V, r13V, r14V, r15V, readyV, frameV⟩
  rw [rspU] at frameV
  have through (address : BitVec 64) (size : Nat)
      (writes : ∀ i < size, ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec direction
        (selected byte shift) (address + BitVec.ofNat 64 i))
      (call : ∀ i < size, ¬CallWrites s c (address + BitVec.ofNat 64 i)) :
      v.data.dmem.loadInt address size = s.dmem.loadInt address size :=
    ((frameU.loadInt address size writes).trans (frameV.loadInt address size call)).symm
  have entryV : Third.Entry v.data parentIndex parentShift parentByte := {
    indexRead := by
      rw [rbxV, rbxU, through _ 1 (fun i hi => (readsApart _ (.inl ⟨i, hi, rfl⟩)).1)
        (fun i hi => (readsApart _ (.inl ⟨i, hi, rfl⟩)).2)]
      exact indexRead
    shiftRead := by
      rw [rbxV, rbxU, through _ 1 (fun i hi => (readsApart _ (.inr (.inl ⟨i, hi, rfl⟩))).1)
        (fun i hi => (readsApart _ (.inr (.inl ⟨i, hi, rfl⟩))).2)]
      exact shiftRead
    byteRead := by
      rw [r12V, r12U, through _ 1 (fun i hi => (readsApart _ (.inr (.inr ⟨i, hi, rfl⟩))).1)
        (fun i hi => (readsApart _ (.inr (.inr ⟨i, hi, rfl⟩))).2)]
      exact byteRead
    indexBound := indexBound
    shiftBound := shiftBound
    byteBound := byteBound
    nodeParentMapped := by
      rw [r12V, r12U, ←frameV.loadInt _ 8 (fun i hi => wordsApart _ (.inl ⟨i, hi, rfl⟩)), memU]
      exact connected_mapped s.dmem _ _ _ _ _ _ _ nodeParentMapped
    leftMapped := by
      rw [rbxV, rbxU, ←frameV.loadInt _ 8 (fun i hi => wordsApart _ (.inr (.inl ⟨i, hi, rfl⟩))), memU]
      exact connected_mapped s.dmem _ _ _ _ _ _ _ parentLeft
    rightMapped := by
      rw [rbxV, rbxU, ←frameV.loadInt _ 8 (fun i hi => wordsApart _ (.inr (.inr ⟨i, hi, rfl⟩))), memU]
      exact connected_mapped s.dmem _ _ _ _ _ _ _ parentRight }
  have pcV' : v.pc = Add.entry + 0x391 := pcV.trans (by rfl)
  rw [Binary.Pair.Allowedips.Placement.at_pc v _ pcV']
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Third.third_connect fetch agree v.data parentIndex parentShift parentByte entryV)
  rintro t ⟨pcT, memT, rbxT, rspT, rbpT, r12T, r13T, r14T, r15T⟩
  have memT' : t.data.dmem = (v.data.dmem.storeInt (s.regs.r12.toBitVec + 48) 8
      (packed s.regs.rbx.toBitVec (selected parentByte parentShift)).toInt).storeInt
      (slot s.regs.rbx.toBitVec (selected parentByte parentShift)) 8 s.regs.r12.toBitVec.toInt := by
    simpa only [Third.mem3, r12V, r12U, rbxV, rbxU] using memT
  have frame3 : EqualOutside (fun a => InRange (s.regs.r12.toBitVec + 48) 8 a ∨
      InRange (slot s.regs.rbx.toBitVec (selected parentByte parentShift)) 8 a) v.data.dmem t.data.dmem := by
    intro a outside
    rw [memT']
    exact (storeInt_frame _ _ _ _ a (fun h => outside (.inl h))).trans
      (storeInt_frame _ _ _ _ a (fun h => outside (.inr h)))
  have readyT : CallsReady c t.data := readyV.frame rspT frame3
    (fun _ _ h => by rw [memT']; exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ h))
    contextApart3
  have total : EqualOutside (PathWrites s c direction (selected byte shift) (selected parentByte parentShift))
      s.dmem t.data.dmem := by
    intro a outside
    exact ((frameU a (fun h => outside (.inl h))).trans
      (frameV a (fun h => outside (.inr (.inl h))))).trans (frame3 a (fun h => outside (.inr (.inr h))))
  rw [memU] at frameV
  exact ⟨v.data.dmem, frameV, pcT, memT', rbxT, rspT.trans (rspV.trans rspU), rbpT.trans (rbpV.trans rbpU),
    r12T.trans (r12V.trans r12U), r13T.trans (r13V.trans r13U), r14T.trans (r14V.trans r14U),
    r15T.trans (r15V.trans r15U), readyT, total⟩

#print axioms connections_nonnull
end Binary.SplitStage3.Path
