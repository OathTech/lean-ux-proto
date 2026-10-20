import Regions

namespace Binary.Lookup
local instance : Labels := Image.linkedLabels

def preemptAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c8
def bucketWord (s : MachineData) : BitVec 32 := s.regs.get (.low .r12 .W32) &&& 8191
def bucketAddress (s : MachineData) : BitVec 64 :=
  s.regs.rbx.toBitVec + (bucketWord s).setWidth 64 * 8
def bhDisabledMemory (s : MachineData) (count : UInt32) : DataMem :=
  s.dmem.storeInt preemptAddress 4 (BitVec.ofInt 32 (512 + count.toNat)).toInt

private theorem truncate_extend (v : BitVec 64) :
    (v.extractLsb' 0 32 |>.setWidth 64).extractLsb' 0 32 = v.extractLsb' 0 32 := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

private theorem of_bmod (n : Nat) :
    BitVec.ofInt 64 ((n : Int).bmod 18446744073709551616) = BitVec.ofNat 64 n := by
  simpa only [BitVec.toInt_ofNat'] using
    (BitVec.ofInt_toInt (x := BitVec.ofNat 64 n))

private theorem of_mask (v : UInt64) :
    BitVec.ofNat 64 (v.toNat % 4294967296 % 18446744073709551616 &&& 8191) =
      (v.toBitVec.extractLsb' 0 32).setWidth 64 &&& 8191#64 := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem of_low32 (v : UInt64) :
    BitVec.ofNat 64 (v.toNat % 4294967296 % 18446744073709551616) =
      (v.toBitVec.extractLsb' 0 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem u64_zero (v : UInt64) : v.toBitVec = 0#64 ↔ v = 0 := UInt64.toBitVec_inj

/-- The caller may already have BH disabled. Count is arbitrary here;
    no zero-count hypothesis excludes nested callers. The head-read fact
    after the update is discharged from separated cells at composition. -/
theorem bucket_entry (s : MachineData) (count : UInt32) (head : UInt64)
    (preempt : s.dmem.loadInt preemptAddress 4 = some count.toNat)
    (first : (bhDisabledMemory s count).loadInt (bucketAddress s) 8 = some head.toNat) :
    (run Image.Lookup.r19 0x19 s).All (fun t =>
      t.data.regs = {s.regs with rax := .ofBitVec ((bucketWord s).setWidth 64), rbx := head} ∧
      t.data.dmem = bhDisabledMemory s count ∧
      t.pc = if head = 0 then Image.Lookup.entry + 0x6c else Image.Lookup.entry + 0x34) := by
  simp [run, Image.Lookup.r19, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.drop, BitVec.take,
     ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    Effects.All, StatusFlags.from_result, CondCode.interp,
    bucketWord, bucketAddress, bhDisabledMemory, preemptAddress, Image.Lookup.entry] at preempt first ⊢
  simp_all [Effects.All, of_bmod,  of_low32, truncate_extend,
    BitVec.toInt_eq_toNat_bmod]
  by_cases hz : head = 0
  all_goals simp_all [Effects.All, u64_zero]
  all_goals try rfl

theorem mask13 (q : Nat) :
    (BitVec.ofNat 32 q &&& 8191#32).toNat = q % 8192 := by
  change (q % 2^32) &&& (2^13 - 1) = q % 2^13
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_mod_of_dvd q (by decide)

#print axioms bucket_entry
#print axioms mask13
end Binary.Lookup
