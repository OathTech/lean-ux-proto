import AllowedipsRootChecked
import AllowedipsReturnFrame
import AllowedipsPlacementPrefix
/-! Result C1, package 2 (origin: trial T4, `task/binary-trials:binary-trials/t4`, copied): the prologue of `add` (entry to the first coverage call at +0x25). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def prologueCode : List (Kraken.Sized Directive) := Add.r00 ++ Add.r14.take 6

theorem prologue_layout : LaidOut Add.fetch (Add.entry + .ofNat 0) prologueCode := by
  unfold prologueCode
  binary_layout

/-- Slots written by the prologue: six pushes, the saved root-slot argument
(8 bytes at final rsp+8) and the saved cidr (4 bytes at final rsp+16). -/
def slot (s : MachineData) (i : Nat) : BitVec 64 :=
  s.regs.rsp.toBitVec - .ofNat 64 (if i<6 then (i+1)*8 else if i=6 then 88 else 80)

def slotSize (i : Nat) : Nat := if i=7 then 4 else 8

def words (s : MachineData) : List UInt64 :=
  [s.regs.r15, s.regs.r14, s.regs.r13, s.regs.r12, s.regs.rbp, s.regs.rbx, s.regs.rdi]

def slotValue (s : MachineData) (i : Nat) : Int :=
  if i=7 then (BitVec.extractLsb' 0 32 s.regs.rcx.toBitVec).toInt
  else ((words s)[i]?.getD 0).toBitVec.toInt

def memory (s : MachineData) : Nat → Mem 64
  | 0 => s.dmem
  | n+1 => (memory s n).storeInt (slot s n) (slotSize n) (slotValue s n)

theorem memory_mapped (s : MachineData) (n k : Nat) (a : BitVec 64)
    (mapped : (s.dmem.loadInt a k).isSome = true) :
    ((memory s n).loadInt a k).isSome = true := by
  induction n with
  | zero => exact mapped
  | succ n ih => exact storeInt_defined _ _ _ _ _ _ ih

theorem prologue (s : MachineData)
    (stack : ∀ i < 8, (s.dmem.loadInt (slot s i) (slotSize i)).isSome = true) :
    (Placement.physical prologueCode 0 s).All (fun t =>
      t.data.regs = {s.regs with
        r15 := .ofBitVec ((s.regs.get (.low .rcx .W32)).setWidth 64),
        r14 := s.regs.r8, r13 := s.regs.rdx,
        r12 := .ofBitVec ((s.regs.get (.low .rcx .W32)).setWidth 64),
        rbp := .ofBitVec ((s.regs.get (.low .rsi .W32)).setWidth 64),
        rsp := s.regs.rsp-96} ∧
      t.data.dmem = memory s 8 ∧ t.pc = Add.entry+0x25) := by
  have mapped (n : Nat) (hn : n<8) := memory_mapped s n _ _ (stack n hn)
  have h0 := mapped 0 (by decide)
  have h1 := mapped 1 (by decide)
  have h2 := mapped 2 (by decide)
  have h3 := mapped 3 (by decide)
  have h4 := mapped 4 (by decide)
  have h5 := mapped 5 (by decide)
  have h6 := mapped 6 (by decide)
  have h7 := mapped 7 (by decide)
  simp only [Option.isSome_iff_exists] at h0 h1 h2 h3 h4 h5 h6 h7
  obtain ⟨v0,h0⟩ := h0
  obtain ⟨v1,h1⟩ := h1
  obtain ⟨v2,h2⟩ := h2
  obtain ⟨v3,h3⟩ := h3
  obtain ⟨v4,h4⟩ := h4
  obtain ⟨v5,h5⟩ := h5
  obtain ⟨v6,h6⟩ := h6
  obtain ⟨v7,h7⟩ := h7
  simp [Placement.physical, prologueCode, Add.r00, Add.r14, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, ConstExpr.interp,
    AddrExpr.interp, BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_add,
    Effects.All, Width.bytesv, Add.entry,
    memory, words, slot, slotSize, slotValue, BitVec.sub_sub] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  simp_all [Effects.All]
  have addressCast (a : BitVec 64) : BitVec.ofInt 64 ((a.toInt-96).bmod 18446744073709551616) = a-96 := by
    have value := BitVec.toInt_sub (x:=a) (y:=96#64)
    change (a-96).toInt = (a.toInt-96).bmod 18446744073709551616 at value
    rw [← value]
    exact BitVec.ofInt_toInt
  simp only [addressCast]
  have address8 (a : BitVec 64) : a-96#64+8#64=a-88#64 := by
    have h : 96#64 = 88#64+8#64 := rfl
    rw [h, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have address16 (a : BitVec 64) : a-96#64+16#64=a-80#64 := by
    have h : 96#64 = 80#64+16#64 := rfl
    rw [h, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  simp only [BitVec.ofNat_eq_ofNat] at *
  rw [address8, address16]
  simp only [h6, h7, Effects.All]
  decide

#print axioms prologue

end C1Trunk
