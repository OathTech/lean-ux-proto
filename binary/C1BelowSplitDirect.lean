import C1BelowSplitSetup
import AllowedipsChild
import Memory
import MemoryBytes

/- Origin: trial source binary-trials/t1/Direct.lean (copied in t5) on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
namespace Binary.SplitStage3.Direct
open AllowedipsMutationImage TrustBase AllowedipsChild
local instance : Labels := Image.linkedLabels

def mem1 (s : MachineData) (direction : Nat) : DataMem :=
  (s.dmem.storeInt (s.regs.rdi.toBitVec + 48) 8 (packed s.regs.r12.toBitVec direction).toInt).storeInt
      (slot s.regs.r12.toBitVec direction) 8 s.regs.rdi.toBitVec.toInt

theorem packed_comm (p : BitVec 64) (b : Nat) : packed p b = .ofNat 64 b ||| slot p b :=
  BitVec.or_comm _ _

theorem regionA (s : MachineData) (direction byteIndex shift : Nat)
    (directionBound : direction < 2)
    (rax : s.regs.rax = .ofNat direction)
    (rdx : s.regs.rdx = .ofNat direction)
    (rcx : s.regs.rcx = .ofNat (direction + 1))
    (indexBound : byteIndex < 16) (shiftBound : shift < 8)
    (downMapped : (s.dmem.loadInt (s.regs.rdi.toBitVec + 48) 8).isSome = true)
    (slotMapped : ((s.dmem.storeInt (s.regs.rdi.toBitVec + 48) 8
        (packed s.regs.r12.toBitVec direction).toInt).loadInt (slot s.regs.r12.toBitVec direction) 8).isSome = true)
    (indexRead : (mem1 s direction).loadInt (s.regs.r12.toBitVec + 25) 1 = some (byteIndex : Int))
    (shiftRead : (mem1 s direction).loadInt (s.regs.r12.toBitVec + 26) 1 = some (shift : Int)) :
    (Directives.interp Add.r338 s (Add.entry + 0x338) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x35a ∧ t.data.dmem = mem1 s direction ∧
      t.data.regs = {s.regs with rax := .ofNat byteIndex, rcx := .ofNat shift}) := by
  obtain ⟨old, oldRead⟩ := Option.isSome_iff_exists.mp downMapped
  obtain ⟨old2, oldRead2⟩ := Option.isSome_iff_exists.mp slotMapped
  have ix := extend8 byteIndex (by omega)
  have sh := extend8 shift (by omega)
  change (BitVec.ofNat 8 byteIndex).setWidth 64 = BitVec.ofNat 64 byteIndex at ix
  change (BitVec.ofNat 8 shift).setWidth 64 = BitVec.ofNat 64 shift at sh
  obtain rfl | rfl : direction = 0 ∨ direction = 1 := by omega
  all_goals
    simp [Add.r338,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    mem1,packed_comm,slot,BitVec.add_assoc,rax,rdx,rcx] at oldRead oldRead2 indexRead shiftRead ⊢
  all_goals rw [oldRead]
  all_goals simp only [Effects.All]
  all_goals rw [oldRead2]
  all_goals simp only [Effects.All]
  all_goals rw [indexRead]
  all_goals simp only [Effects.All]
  all_goals rw [shiftRead]
  all_goals simp [Effects.All, Add.entry, BitVec.ofInt_natCast, ix, sh]
  all_goals exact ⟨rfl, rfl⟩

theorem regionB (s : MachineData) (byteIndex shift byte : Nat)
    (rax : s.regs.rax = .ofNat byteIndex) (rcx : s.regs.rcx = .ofNat shift)
    (shiftBound : shift < 8) (byteBound : byte < 256)
    (byteRead : s.dmem.loadInt (s.regs.r8.toBitVec + 32 + .ofNat 64 byteIndex) 1 = some (byte : Int)) :
    (Directives.interp Add.r35a s (Add.entry + 0x35a) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x373 ∧ t.data.dmem = s.dmem ∧
      t.data.regs = {s.regs with rax := UInt64.ofNat (selected byte shift), rcx := UInt64.ofNat (selected byte shift + 1), rdx := UInt64.ofNat (selected byte shift)}) := by
  have byteAddr : s.regs.r8.toBitVec + BitVec.ofNat 64 byteIndex + 32 =
      s.regs.r8.toBitVec + 32 + BitVec.ofNat 64 byteIndex := by ac_rfl
  simp at byteAddr byteRead
  obtain ⟨b, rfl⟩ : ∃ b : Fin 256, byte = b.val := ⟨⟨byte, byteBound⟩, rfl⟩
  rcases (by omega : shift = 0 ∨ shift = 1 ∨ shift = 2 ∨ shift = 3 ∨ shift = 4 ∨ shift = 5 ∨
    shift = 6 ∨ shift = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [Add.r35a, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
     ConstExpr.interp,  AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    UInt64.toBitVec_ofNat', BitVec.ofInt_add, BitVec.ofInt_toInt,
    byteAddr, byteRead, rax, rcx,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp]
  all_goals clear byteRead byteBound
  all_goals refine ⟨rfl, ?_⟩
  all_goals revert b
  all_goals decide +kernel

def mem2 (s : MachineData) (bit : Nat) : DataMem :=
  (s.dmem.storeInt (s.regs.r8.toBitVec + 48) 8 (packed s.regs.r12.toBitVec bit).toInt).storeInt
      (slot s.regs.r12.toBitVec bit) 8 s.regs.r8.toBitVec.toInt

theorem regionC (s : MachineData) (bit : Nat)
    (bitBound : bit < 2)
    (rax : s.regs.rax = .ofNat bit)
    (rdx : s.regs.rdx = .ofNat bit)
    (rcx : s.regs.rcx = .ofNat (bit + 1))
    (newMapped : (s.dmem.loadInt (s.regs.r8.toBitVec + 48) 8).isSome = true)
    (slotMapped : ((s.dmem.storeInt (s.regs.r8.toBitVec + 48) 8
        (packed s.regs.r12.toBitVec bit).toInt).loadInt (slot s.regs.r12.toBitVec bit) 8).isSome = true) :
    (Directives.interp Add.r373 s (Add.entry + 0x373) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = (if s.regs.rbx = 0 then Add.entry + 0x6c0 else Add.entry + 0x38c) ∧
      t.data.dmem = mem2 s bit ∧
      t.data.regs = {s.regs with rcx := UInt64.ofBitVec (slot s.regs.r12.toBitVec bit), rdx := UInt64.ofBitVec (packed s.regs.r12.toBitVec bit)}) := by
  obtain ⟨old, oldRead⟩ := Option.isSome_iff_exists.mp newMapped
  obtain ⟨old2, oldRead2⟩ := Option.isSome_iff_exists.mp slotMapped
  have zeroIff : s.regs.rbx = 0 ↔ s.regs.rbx.toBitVec = 0#64 := by
    rw [← UInt64.toBitVec_inj]; rfl
  obtain rfl | rfl : bit = 0 ∨ bit = 1 := by omega
  all_goals
    simp [Add.r373,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    mem2,packed_comm,slot,BitVec.add_assoc,rax,rdx,rcx] at oldRead oldRead2 ⊢
  all_goals rw [oldRead]
  all_goals simp only [Effects.All]
  all_goals rw [oldRead2]
  all_goals simp only [Effects.All]
  all_goals intro v
  all_goals by_cases h : s.regs.rbx.toBitVec = 0#64
  all_goals simp [h, zeroIff, CondCode.interp, StatusFlags.from_result, Effects.All]
  all_goals rfl

theorem load_frame2 (m : Mem 64) (a1 a2 : BitVec 64) (v1 v2 : Int) (base : BitVec 64) (len : Nat)
    (h1 : ∀ i < len, ¬InRange a1 8 (base + .ofNat 64 i))
    (h2 : ∀ i < len, ¬InRange a2 8 (base + .ofNat 64 i)) :
    ((m.storeInt a1 8 v1).storeInt a2 8 v2).loadInt base len = m.loadInt base len :=
  (((storeInt_frame m a1 8 v1).trans (storeInt_frame _ a2 8 v2)).loadInt base len
    (fun i hi h => h.elim (h1 i hi) (h2 i hi))).symm

theorem inObject (p : BitVec 64) (off len : Nat) (h : off + len ≤ nodeSize) (a : BitVec 64)
    (inside : InRange (p + .ofNat 64 off) len a) : InRange p nodeSize a := by
  obtain ⟨i, hi, rfl⟩ := inside
  exact ⟨off + i, by omega, by rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩

theorem slot_mapped (m : Mem 64) (p : BitVec 64) (b : Nat) (bound : b < 2)
    (left : (m.loadInt (p + 8) 8).isSome = true) (right : (m.loadInt (p + 16) 8).isSome = true) :
    (m.loadInt (slot p b) 8).isSome = true := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact left
  · exact right

theorem slot_inObject (p : BitVec 64) (b : Nat) (bound : b < 2) (a : BitVec 64)
    (inside : InRange (slot p b) 8 a) : InRange p nodeSize a :=
  inObject p (8 + 8 * b) 8 (by unfold nodeSize; omega) a inside

theorem selected_bound (byte shift : Nat) : selected byte shift < 2 := by
  unfold selected; omega

theorem target : SplitTarget.Statement := by
  intro fetch agree s direction byteIndex shift byte entry
  have dB := entry.directionBound
  -- frame facts for reads of `node` and `newnode` after the first two stores
  have nodeField : ∀ off, 25 ≤ off → off < 27 →
      (mem1 s direction).loadInt (s.regs.r12.toBitVec + .ofNat 64 off) 1 =
        s.dmem.loadInt (s.regs.r12.toBitVec + .ofNat 64 off) 1 := by
    intro off lo hi
    apply load_frame2
    · intro i hi' inDown
      have h1 : InRange s.regs.r12.toBitVec nodeSize (s.regs.r12.toBitVec + .ofNat 64 off + .ofNat 64 i) :=
        inObject _ off 1 (by unfold nodeSize; omega) _ ⟨i, hi', rfl⟩
      exact entry.nodeDown _ h1 (inObject _ 48 8 (by unfold nodeSize; omega) _ inDown)
    · intro i hi' inSlot
      exact InRange.offset_disjoint s.regs.r12.toBitVec off 1 (8 + 8 * direction) 8
        (by omega) (by omega) (by omega) _ ⟨i, hi', rfl⟩ inSlot
  have byteFrame : (mem1 s direction).loadInt (s.regs.r8.toBitVec + 32 + .ofNat 64 byteIndex) 1 =
      some (byte : Int) := by
    rw [← entry.byteRead]
    apply load_frame2
    · intro i hi' inDown
      have h1 : InRange s.regs.r8.toBitVec nodeSize
          (s.regs.r8.toBitVec + 32 + .ofNat 64 byteIndex + .ofNat 64 i) := by
        refine ⟨32 + byteIndex + i, by have := entry.indexBound; unfold nodeSize; omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      exact entry.downNew _ (inObject _ 48 8 (by unfold nodeSize; omega) _ inDown) h1
    · intro i hi' inSlot
      have h1 : InRange s.regs.r8.toBitVec nodeSize
          (s.regs.r8.toBitVec + 32 + .ofNat 64 byteIndex + .ofNat 64 i) := by
        refine ⟨32 + byteIndex + i, by have := entry.indexBound; unfold nodeSize; omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      exact entry.nodeNew _ (slot_inObject _ direction dB _ inSlot) h1
  have first := regionA s direction byteIndex shift dB entry.rax entry.rdx entry.rcx
    entry.indexBound entry.shiftBound entry.downParentMapped
    (storeInt_defined _ _ _ _ _ _ (slot_mapped _ _ _ dB entry.leftMapped entry.rightMapped))
    ((nodeField 25 (by omega) (by omega)).trans entry.indexRead)
    ((nodeField 26 (by omega) (by omega)).trans entry.shiftRead)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (r338_layout agree) s _ first)
  rintro ⟨a, apc⟩ ⟨pcA, memA, regsA⟩
  simp only at pcA memA regsA
  subst pcA
  have second := regionB a byteIndex shift byte (by rw [regsA]) (by rw [regsA])
    entry.shiftBound entry.byteBound (by rw [memA, regsA]; exact byteFrame)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (r35a_layout agree) a _ second)
  rintro ⟨b, bpc⟩ ⟨pcB, memB, regsB⟩
  simp only at pcB memB regsB
  subst pcB
  have sB := selected_bound byte shift
  have third := regionC b (selected byte shift) sB (by rw [regsB]) (by rw [regsB]) (by rw [regsB])
    (by rw [memB, memA, regsB, regsA]
        exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ entry.newParentMapped))
    (by rw [memB, memA, regsB, regsA]
        exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _
          (slot_mapped _ _ _ sB entry.leftMapped entry.rightMapped))))
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (r373_layout agree) b _ third)
  rintro t ⟨pcT, memT, regsT⟩
  simp only [Exit, pcT, memT, regsT, mem2, memB, memA, mem1, regsB, regsA, connected]
  simp only [and_self]

#print axioms target

end Binary.SplitStage3.Direct
