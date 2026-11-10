import AllowedipsPlacementRegions
import AllowedipsChild
import RegionExecution
import MemoryBytes

/-! Result C1, work package 3, covering path: the straight-line regions from
the comparison at `add+0x267` to the common exit, as executions of the
image's directives. No call is stepped here. -/
namespace Binary.Pair.Allowedips.C1Cover
open AllowedipsMutationImage TrustBase AllowedipsChild Placement
local instance : Labels := Image.linkedLabels

/-- `+0x267`: `cmp 0x10(%rsp),%r13b; mov 0x18(%rsp),%r8; jae +0x56d`. -/
theorem compare_step (s : MachineData) (cidr : BitVec 8) (base : BitVec 64)
    (cidrRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x10) 1=some cidr.toNat)
    (baseRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some base.toNat) :
    (physical Add.r267 0x267 s).All (fun t =>
      t.data.regs={s.regs with r8 := .ofBitVec base} ∧ t.data.dmem=s.dmem ∧
      t.pc=if cidr.toNat ≤ (s.regs.get (.low .r13 .W8)).toNat
        then Add.entry+0x56d else Add.entry+0x277) := by
  simp [physical,Add.r267,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get64,Reg64s.set,Reg64s.set64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    StatusFlags.from_result,CondCode.interp,Allowedips.carry8] at cidrRead baseRead ⊢
  rw [cidrRead]
  simp only [Effects.All]
  rw [baseRead]
  simp only [Effects.All]
  have target : (label "L_ffffffff813a112d" : Int64)=Add.entry+0x56d := by decide +kernel
  have small : (cidr.toNat : Int) % 256=cidr.toNat := by have := cidr.isLt; omega
  simp only [small,Int.ofNat_le,target]
  split <;> simp_all [Effects.All,Add.entry,BitVec.ofInt_natCast]

#print axioms compare_step

/-- `+0x56d`: `mov %r8,0x10(%rsp)`, up to the coverage call at `+0x572`. -/
theorem save_step (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec+0x10) 8).isSome=true) :
    (physical (Add.r56d.take 1) 0x56d s).All (fun t =>
      t.pc=Add.entry+0x572 ∧ t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec+0x10) 8 s.regs.r8.toBitVec.toInt) := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  simp [physical,Add.r56d,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at read ⊢
  rw [read]
  simp [Effects.All,Add.entry]

#print axioms save_step

/-- `&parent->bit[bit]`: the two child pointers are at offsets 8 and 16. -/
def slot (parent : BitVec 64) (bit : Nat) : BitVec 64 := parent + .ofNat 64 (8 + 8 * bit)

/-- `parent_bit_packed` as `connect_node` stores it. -/
def packed (parent : BitVec 64) (bit : Nat) : BitVec 64 := slot parent bit ||| .ofNat 64 bit

theorem packed_comm (p : BitVec 64) (b : Nat) : packed p b = .ofNat 64 b ||| slot p b :=
  BitVec.or_comm _ _

theorem low_bit (byte : BitVec 8) (c : Bool) :
    (BitVec.setWidth 64 byte).replaceLow (BitVec.ofNat 8 c.toNat)=BitVec.ofNat 64 c.toNat := by
  cases c <;> revert byte <;> decide +kernel

/-- `+0x577`: the loads and `choose(newnode, down->bits)` by `bt`. The bit
index is the 32-bit word at `rsp+0x2c` modulo 32; `rdx` keeps that whole word
until the next region's `movzbl %al,%edx`. -/
theorem choose_step (s : MachineData) (down base : BitVec 64) (byteIndex : Nat) (word : BitVec 32)
    (byte : BitVec 8) (bit : Bool) (indexBound : byteIndex<16)
    (downRead : s.dmem.loadInt s.regs.rsp.toBitVec 8=some down.toNat)
    (indexRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x2b) 1=some (byteIndex : Int))
    (shiftRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x2c) 4=some word.toNat)
    (baseRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x10) 8=some base.toNat)
    (byteRead : s.dmem.loadInt (down+32+.ofNat 64 byteIndex) 1=some byte.toNat)
    (chosen : byte.getLsbD (word.toNat%32)=bit) :
    (physical Add.r577 0x577 s).All (fun t =>
      t.pc=Add.entry+0x597 ∧ t.data.dmem=s.dmem ∧
      t.data.regs={s.regs with rax := .ofNat bit.toNat,rcx := .ofNat (bit.toNat+1),rdx := .ofBitVec (word.setWidth 64),rsi := .ofBitVec down,r8 := .ofBitVec base}) := by
  have ix := extend8 byteIndex (by omega)
  change (BitVec.ofNat 8 byteIndex).setWidth 64 = BitVec.ofNat 64 byteIndex at ix
  have byteAddr : down + BitVec.ofNat 64 byteIndex + 32#64 = down + 32#64 + BitVec.ofNat 64 byteIndex := by ac_rfl
  have idx : BitVec.ofInt 64 ((max ((byteIndex : Int) % 256) 0).bmod 18446744073709551616) =
      BitVec.ofNat 64 byteIndex := by
    have h1 : (byteIndex : Int) % 256 = byteIndex := by omega
    have h2 : max (byteIndex : Int) 0 = byteIndex := by omega
    rw [h1, h2, AllowedipsChild.ofInt_bmod64]
    rfl
  have downEq : BitVec.ofInt 64 ((down.toNat : Int).bmod 18446744073709551616) = down := by
    rw [AllowedipsChild.ofInt_bmod64]; simp [BitVec.ofInt_natCast]
  have wordEq : ((word.toNat : Int) % 4294967296).toNat = word.toNat := by have := word.isLt; omega
  have inRange : word.toNat%32<32 := Nat.mod_lt _ (by decide)
  subst chosen
  simp [physical,Add.r577,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All]
    at downRead indexRead shiftRead baseRead byteRead ⊢
  rw [downRead]
  simp only [Effects.All]
  rw [indexRead]
  simp only [Effects.All]
  rw [shiftRead]
  simp only [Effects.All]
  rw [baseRead]
  simp [Effects.All,BitVec.ofInt_natCast,idx,downEq,wordEq,inRange,
    (by omega : word.toNat%32<64)]
  rw [byteAddr,byteRead]
  simp only [Effects.All]
  intro pf af zf sf of
  cases h : byte.getLsbD (word.toNat%32)
  all_goals simp [h,CondCode.interp,Effects.All,Add.entry,BitVec.ofInt_natCast]
  · have low : (BitVec.setWidth 64 byte).replaceLow 0#8=0#64 := low_bit byte false
    rw [low]
    exact ⟨rfl,rfl⟩
  · have low : (BitVec.setWidth 64 byte).replaceLow 1#8=1#64 := low_bit byte true
    rw [low]
    exact ⟨rfl,rfl⟩

#print axioms choose_step

/-- The memory after `choose_and_connect_node(newnode, down)` with the save of
`newnode` between its two stores, in the image's order. -/
def mem1 (m : DataMem) (stack down base : BitVec 64) (bit : Nat) : DataMem :=
  ((m.storeInt (down+48) 8 (packed base bit).toInt).storeInt stack 8 base.toInt).storeInt
    (slot base bit) 8 down.toInt

/-- `+0x597`: the packed parent word into `down`, the save of `newnode`. -/
theorem link_step (s : MachineData) (bit : Nat) (bitBound : bit<2)
    (rax : s.regs.rax = .ofNat bit) (rcx : s.regs.rcx = .ofNat (bit+1))
    (parentMapped : (s.dmem.loadInt (s.regs.rsi.toBitVec+48) 8).isSome=true)
    (stackMapped : ((s.dmem.storeInt (s.regs.rsi.toBitVec+48) 8 (packed s.regs.r8.toBitVec bit).toInt).loadInt
      s.regs.rsp.toBitVec 8).isSome=true) :
    (physical Add.r597 0x597 s).All (fun t =>
      t.pc=Add.entry+0x5b2 ∧
      t.data.dmem=(s.dmem.storeInt (s.regs.rsi.toBitVec+48) 8 (packed s.regs.r8.toBitVec bit).toInt).storeInt
        s.regs.rsp.toBitVec 8 s.regs.r8.toBitVec.toInt ∧
      t.data.regs={s.regs with rax := .ofNat bit,rcx := .ofBitVec (slot s.regs.r8.toBitVec bit),rdx := .ofNat bit}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp parentMapped
  obtain ⟨old1,oldRead1⟩ := Option.isSome_iff_exists.mp stackMapped
  obtain rfl | rfl : bit = 0 ∨ bit = 1 := by omega
  all_goals
    simp [physical,Add.r597,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    packed_comm,slot,rax,rcx] at oldRead oldRead1 ⊢
  all_goals rw [oldRead]
  all_goals simp only [Effects.All]
  all_goals rw [oldRead1]
  all_goals simp [Effects.All,Add.entry]
  all_goals rfl

#print axioms link_step

/-- `+0x5b2`: `newnode->bit[bit] := down`, then the test of `parent`. -/
theorem slot_step (s : MachineData) (bit : Nat) (bitBound : bit<2)
    (rax : s.regs.rax = .ofNat bit)
    (slotMapped : (s.dmem.loadInt (slot s.regs.r8.toBitVec bit) 8).isSome=true) :
    (physical Add.r5b2 0x5b2 s).All (fun t =>
      t.pc=(if s.regs.rbx=0 then Add.entry+0x71d else Add.entry+0x5c0) ∧
      t.data.dmem=s.dmem.storeInt (slot s.regs.r8.toBitVec bit) 8 s.regs.rsi.toBitVec.toInt ∧
      t.data.regs=s.regs) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp slotMapped
  have zeroIff : s.regs.rbx = 0 ↔ s.regs.rbx.toBitVec = 0#64 := by
    rw [← UInt64.toBitVec_inj]; rfl
  have target : (label "L_ffffffff813a12dd" : Int64)=Add.entry+0x71d := by decide +kernel
  obtain rfl | rfl : bit = 0 ∨ bit = 1 := by omega
  all_goals
    simp [physical,Add.r5b2,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    slot,BitVec.add_assoc,rax] at oldRead ⊢
  all_goals rw [oldRead]
  all_goals simp only [Effects.All]
  all_goals intro v
  all_goals by_cases h : s.regs.rbx.toBitVec = 0#64
  all_goals simp [h, zeroIff, CondCode.interp, StatusFlags.from_result, Effects.All, target]
  all_goals rfl

#print axioms slot_step

theorem ofInt_nat (x : BitVec 64) : BitVec.ofInt 64 ((x.toNat : Int).bmod 18446744073709551616)=x := by
  rw [AllowedipsChild.ofInt_bmod64]; simp [BitVec.ofInt_natCast]

theorem nat_mod (x : BitVec 64) : ((x.toNat : Int) % 18446744073709551616).toNat=x.toNat := by
  have := x.isLt; omega

/-- `+0x722` (no parent): the root slot's address from the stack, the fresh
node's parent word `slot|2`, the slot itself. -/
theorem root_step (s : MachineData) (rootSlot base : BitVec 64)
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some rootSlot.toNat)
    (baseRead : s.dmem.loadInt s.regs.rsp.toBitVec 8=some base.toNat)
    (parentMapped : (s.dmem.loadInt (base+48) 8).isSome=true)
    (slotMapped : ((s.dmem.storeInt (base+48) 8 (rootSlot ||| 2#64).toInt).loadInt rootSlot 8).isSome=true) :
    (physical Add.r722 0x722 s).All (fun t =>
      t.pc=Add.entry+0x549 ∧
      t.data.dmem=(s.dmem.storeInt (base+48) 8 (rootSlot ||| 2#64).toInt).storeInt rootSlot 8 base.toInt ∧
      t.data.regs={s.regs with rax := .ofBitVec (rootSlot ||| 2#64),rbx := 0,rdx := .ofBitVec rootSlot,r8 := .ofBitVec base}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp parentMapped
  obtain ⟨old1,oldRead1⟩ := Option.isSome_iff_exists.mp slotMapped
  have target : (label "L_ffffffff813a1109" : Int64)=Add.entry+0x549 := by decide +kernel
  simp [physical,Add.r722,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,Effects.All,
    BitVec.ofInt_ofNat] at slotRead baseRead oldRead oldRead1 ⊢
  rw [slotRead]
  simp only [Effects.All]
  rw [baseRead]
  simp [Effects.All,ofInt_nat,nat_mod]
  rw [oldRead]
  simp only [Effects.All]
  intro af
  rw [oldRead1]
  simp [RelRegOrMem.interp,ConstExpr.interp,Effects.All,target]
  refine ⟨by rfl,?_⟩
  rw [BitVec.toInt_eq_toNat_bmod]

#print axioms root_step

/-- `+0x5c5` (below a parent): `choose(parent, newnode->bits)`. -/
theorem parent_choose_step (s : MachineData) (base : BitVec 64) (byteIndex shift byte : Nat)
    (indexBound : byteIndex < 16) (shiftBound : shift < 8) (byteBound : byte < 256)
    (indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 25) 1 = some (byteIndex : Int))
    (baseRead : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some base.toNat)
    (shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 26) 1 = some (shift : Int))
    (byteRead : s.dmem.loadInt (base + 32 + .ofNat 64 byteIndex) 1 = some (byte : Int)) :
    (physical Add.r5c5 0x5c5 s).All (fun t =>
      t.pc = Add.entry + 0x5e1 ∧ t.data.dmem = s.dmem ∧
      t.data.regs = {s.regs with rax := UInt64.ofNat (selected byte shift), rcx := UInt64.ofNat shift, rdx := UInt64.ofNat (selected byte shift), r8 := .ofBitVec base}) := by
  have ix := extend8 byteIndex (by omega)
  change (BitVec.ofNat 8 byteIndex).setWidth 64 = BitVec.ofNat 64 byteIndex at ix
  have byteAddr : base + BitVec.ofNat 64 byteIndex + 32#64 = base + 32#64 + BitVec.ofNat 64 byteIndex := by ac_rfl
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
    simp [physical, Add.r5c5, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
     ConstExpr.interp,  AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp] at indexRead shiftRead baseRead byteRead ⊢
  all_goals rw [indexRead]
  all_goals simp only [Effects.All]
  all_goals rw [baseRead]
  all_goals simp only [Effects.All]
  all_goals rw [shiftRead]
  all_goals simp [Effects.All, idx, ofInt_nat, byteAddr, byteRead, BitVec.ofInt_natCast]
  all_goals clear byteRead byteBound
  all_goals refine ⟨rfl, ?_⟩
  all_goals revert b
  all_goals decide +kernel

#print axioms parent_choose_step

/-- `+0x5e1` (below a parent): the fresh node's parent word, the parent's
slot, `ebx := 0` and the jump to the common exit. -/
theorem parent_link_step (s : MachineData) (bit : Nat) (bitBound : bit < 2)
    (rax : s.regs.rax = .ofNat bit) (rdx : s.regs.rdx = .ofNat bit)
    (nodeMapped : (s.dmem.loadInt (s.regs.r8.toBitVec + 48) 8).isSome = true)
    (slotMapped : ((s.dmem.storeInt (s.regs.r8.toBitVec + 48) 8
        (packed s.regs.rbx.toBitVec bit).toInt).loadInt (slot s.regs.rbx.toBitVec bit) 8).isSome = true) :
    (physical (Add.r5e1++Add.r5fc) 0x5e1 s).All (fun t =>
      t.pc = Add.entry + 0x549 ∧
      t.data.dmem = (s.dmem.storeInt (s.regs.r8.toBitVec + 48) 8 (packed s.regs.rbx.toBitVec bit).toInt).storeInt
        (slot s.regs.rbx.toBitVec bit) 8 s.regs.r8.toBitVec.toInt ∧
      t.data.regs = {s.regs with rbx := 0, rcx := UInt64.ofBitVec (slot s.regs.rbx.toBitVec bit), rdx := UInt64.ofBitVec (packed s.regs.rbx.toBitVec bit)}) := by
  obtain ⟨old, oldRead⟩ := Option.isSome_iff_exists.mp nodeMapped
  obtain ⟨old2, oldRead2⟩ := Option.isSome_iff_exists.mp slotMapped
  have target : (label "L_ffffffff813a1109" : Int64)=Add.entry+0x549 := by decide +kernel
  obtain rfl | rfl : bit = 0 ∨ bit = 1 := by omega
  all_goals
    simp [physical,Add.r5e1,Add.r5fc,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    packed_comm,slot,BitVec.add_assoc,rax,rdx] at oldRead oldRead2 ⊢
  all_goals rw [oldRead]
  all_goals simp only [Effects.All]
  all_goals rw [oldRead2]
  all_goals simp only [Effects.All]
  all_goals intro v
  all_goals simp [RelRegOrMem.interp,ConstExpr.interp,Effects.All,target]
  all_goals rfl

#print axioms parent_link_step

end Binary.Pair.Allowedips.C1Cover
