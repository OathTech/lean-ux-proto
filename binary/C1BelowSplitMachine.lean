import C1BelowSplitBridge

/- Origin: trial source binary-trials/t5/T5Machine.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 3 (second piece): the image's third connection,
`choose_and_connect_node(parent, node)`, `Add.entry+0x391 .. +0x3ca` (regions
`Add.r391`, `Add.r3ac`; 16 instructions ending in the jump to the common exit). -/
namespace Binary.SplitStage3.Third
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.SplitStage3.Direct
local instance : Labels := Image.linkedLabels

theorem r391_layout {fetch : Int64 → Option Decoded} (mutation : AllowedipsMutationDecoderAgreement fetch) :
    LaidOut fetch (Add.entry + 0x391) Add.r391 := Add_r391_layout.agreement mutation.add

theorem r3ac_layout {fetch : Int64 → Option Decoded} (mutation : AllowedipsMutationDecoderAgreement fetch) :
    LaidOut fetch (Add.entry + 0x3ac) Add.r3ac := Add_r3ac_layout.agreement mutation.add

theorem regionD (s : MachineData) (byteIndex shift byte : Nat)
    (indexBound : byteIndex < 16) (shiftBound : shift < 8) (byteBound : byte < 256)
    (indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 25) 1 = some (byteIndex : Int))
    (shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 26) 1 = some (shift : Int))
    (byteRead : s.dmem.loadInt (s.regs.r12.toBitVec + 32 + .ofNat 64 byteIndex) 1 = some (byte : Int)) :
    (Directives.interp Add.r391 s (Add.entry + 0x391) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x3ac ∧ t.data.dmem = s.dmem ∧
      t.data.regs = {s.regs with rax := UInt64.ofNat (selected byte shift), rcx := UInt64.ofNat (selected byte shift + 1), rdx := UInt64.ofNat (selected byte shift)}) := by
  have ix := extend8 byteIndex (by omega)
  change (BitVec.ofNat 8 byteIndex).setWidth 64 = BitVec.ofNat 64 byteIndex at ix
  have byteAddr : s.regs.r12.toBitVec + BitVec.ofNat 64 byteIndex + 32 =
      s.regs.r12.toBitVec + 32 + BitVec.ofNat 64 byteIndex := by ac_rfl
  simp at byteAddr byteRead
  have idx : BitVec.ofInt 64 ((max ((byteIndex : Int) % 256) 0).bmod 18446744073709551616) =
      BitVec.ofNat 64 byteIndex := by
    have h1 : (byteIndex : Int) % 256 = byteIndex := by omega
    have h2 : max (byteIndex : Int) 0 = byteIndex := by omega
    rw [h1, h2, AllowedipsChild.ofInt_bmod64]
    rfl
  obtain ⟨b, rfl⟩ : ∃ b : Fin 256, byte = b.val := ⟨⟨byte, byteBound⟩, rfl⟩
  rcases (by omega : shift = 0 ∨ shift = 1 ∨ shift = 2 ∨ shift = 3 ∨ shift = 4 ∨ shift = 5 ∨
    shift = 6 ∨ shift = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [Add.r391, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
     ConstExpr.interp,  AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp] at indexRead shiftRead ⊢
  all_goals rw [indexRead]
  all_goals simp only [Effects.All]
  all_goals rw [shiftRead]
  all_goals
    simp [Effects.All, idx, byteAddr, byteRead, BitVec.ofInt_natCast]
  all_goals clear byteRead byteBound
  all_goals refine ⟨rfl, ?_⟩
  all_goals revert b
  all_goals decide +kernel

def mem3 (s : MachineData) (bit : Nat) : DataMem :=
  (s.dmem.storeInt (s.regs.r12.toBitVec + 48) 8 (packed s.regs.rbx.toBitVec bit).toInt).storeInt
      (slot s.regs.rbx.toBitVec bit) 8 s.regs.r12.toBitVec.toInt

theorem regionE (s : MachineData) (bit : Nat)
    (bitBound : bit < 2)
    (rax : s.regs.rax = .ofNat bit)
    (rdx : s.regs.rdx = .ofNat bit)
    (rcx : s.regs.rcx = .ofNat (bit + 1))
    (nodeMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (slotMapped : ((s.dmem.storeInt (s.regs.r12.toBitVec + 48) 8
        (packed s.regs.rbx.toBitVec bit).toInt).loadInt (slot s.regs.rbx.toBitVec bit) 8).isSome = true) :
    (Directives.interp Add.r3ac s (Add.entry + 0x3ac) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x549 ∧
      t.data.dmem = mem3 s bit ∧
      t.data.regs = {s.regs with rbx := 0, rcx := UInt64.ofBitVec (slot s.regs.rbx.toBitVec bit), rdx := UInt64.ofBitVec (packed s.regs.rbx.toBitVec bit)}) := by
  obtain ⟨old, oldRead⟩ := Option.isSome_iff_exists.mp nodeMapped
  obtain ⟨old2, oldRead2⟩ := Option.isSome_iff_exists.mp slotMapped
  obtain rfl | rfl : bit = 0 ∨ bit = 1 := by omega
  all_goals
    simp [Add.r3ac,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    mem3,packed_comm,slot,BitVec.add_assoc,rax,rdx,rcx] at oldRead oldRead2 ⊢
  all_goals rw [oldRead]
  all_goals simp only [Effects.All]
  all_goals rw [oldRead2]
  all_goals simp only [Effects.All]
  all_goals intro v
  all_goals simp [RelRegOrMem.interp,ConstExpr.interp,Effects.All]
  all_goals rfl

#print axioms regionD
#print axioms regionE

/-- The state at `Add.entry + 0x391`: `rbx` is `parent`, `r12` is the internal `node`.
`byteIndex` and `shift` are `parent->bit_at_a` and `parent->bit_at_b`; `byte` is
`node->bits[byteIndex]`. All reads precede the two stores, so no separation is needed. -/
structure Entry (s : MachineData) (byteIndex shift byte : Nat) : Prop where
  indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 25) 1 = some (byteIndex : Int)
  shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 26) 1 = some (shift : Int)
  byteRead : s.dmem.loadInt (s.regs.r12.toBitVec + 32 + .ofNat 64 byteIndex) 1 = some (byte : Int)
  indexBound : byteIndex < 16
  shiftBound : shift < 8
  byteBound : byte < 256
  nodeParentMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true
  leftMapped : (s.dmem.loadInt (s.regs.rbx.toBitVec + 8) 8).isSome = true
  rightMapped : (s.dmem.loadInt (s.regs.rbx.toBitVec + 16) 8).isSome = true

/-- The state at the common exit `Add.entry + 0x549` (`L_ffffffff813a1109`): the two
stores of `connect_node(&parent->bit[bit], bit, node)`, and `rbx` (the return value) zero. -/
def Exit (s : MachineData) (shift byte : Nat) (t : MachineState) : Prop :=
  t.pc = Add.entry + 0x549 ∧
  t.data.dmem = mem3 s (selected byte shift) ∧
  t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧ t.data.regs.rbp = s.regs.rbp ∧
  t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧ t.data.regs.r14 = s.regs.r14 ∧
  t.data.regs.r15 = s.regs.r15

theorem third_connect (fetch : Int64 → Option Decoded) (agree : AllowedipsMutationDecoderAgreement fetch)
    (s : MachineData) (byteIndex shift byte : Nat) (entry : Entry s byteIndex shift byte) :
    Eventually (@instructionStep Image.linkedLabels fetch) (Exit s shift byte) ⟨s, Add.entry + 0x391⟩ := by
  have first := regionD s byteIndex shift byte entry.indexBound entry.shiftBound entry.byteBound
    entry.indexRead entry.shiftRead entry.byteRead
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (r391_layout agree) s _ first)
  rintro ⟨a, apc⟩ ⟨pcA, memA, regsA⟩
  simp only at pcA memA regsA
  subst pcA
  have sB := selected_bound byte shift
  have second := regionE a (selected byte shift) sB (by rw [regsA]) (by rw [regsA]) (by rw [regsA])
    (by rw [memA, regsA]; exact entry.nodeParentMapped)
    (by rw [memA, regsA]
        exact storeInt_defined _ _ _ _ _ _ (slot_mapped _ _ _ sB entry.leftMapped entry.rightMapped))
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (r3ac_layout agree) a _ second)
  rintro t ⟨pcT, memT, regsT⟩
  simp only [Exit, pcT, memT, regsT, mem3, memA, regsA]
  simp only [and_self]

#print axioms third_connect

end Binary.SplitStage3.Third

namespace Binary.Pair.Allowedips.C1Split
open Binary.SplitStage3

/-- The third connection's machine memory in stage 1's terms. -/
theorem mem3_connectMemory (m : DataMem) (node parent bit : Nat) :
    (m.storeInt (BitVec.ofNat 64 node + 48) 8 (packed (.ofNat 64 parent) bit).toInt).storeInt
        (slot (.ofNat 64 parent) bit) 8 (BitVec.ofNat 64 node).toInt=
      connectMemory m node (parent+8+bit*8) ((parent+(bit+1)*8) ||| bit) := by
  simp only [connectMemory,write64,slot_ofNat,packed_ofNat,field_ofNat]

/-- The six stores of the three connections, as the image performs them (t1's four,
then the third connection's two), are the memory of stage 1. -/
theorem machine_memory_stage1 (m : DataMem) (node down newnode parent b1 b2 direction : Nat) :
    ((connected m (.ofNat 64 node) (.ofNat 64 down) (.ofNat 64 newnode) b1 b2).storeInt
        (BitVec.ofNat 64 node + 48) 8 (packed (.ofNat 64 parent) direction).toInt).storeInt
        (slot (.ofNat 64 parent) direction) 8 (BitVec.ofNat 64 node).toInt=
      connectMemory (connectMemory (connectMemory m
          down (node+8+b1*8) ((node+(b1+1)*8) ||| b1))
          newnode (node+8+b2*8) ((node+(b2+1)*8) ||| b2))
          node (parent+8+direction*8) ((parent+(direction+1)*8) ||| direction) := by
  rw [mem3_connectMemory,connected_connectMemory]

#print axioms machine_memory_stage1
end Binary.Pair.Allowedips.C1Split
