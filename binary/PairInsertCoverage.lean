import PairIndexCallMemory

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage

private theorem shifted_mask (n k shift : Nat) :
    n &&& ((2^k-1)*2^shift)=(n/2^shift%2^k)*2^shift := by
  have positive : 0<2^shift := Nat.two_pow_pos shift
  have low : (n &&& ((2^k-1)*2^shift))%2^shift=0 := by
    rw [Nat.and_mod_two_pow]
    simp
  have high : (n &&& ((2^k-1)*2^shift))/2^shift=n/2^shift%2^k := by
    rw [Nat.and_div_two_pow,Nat.mul_div_cancel _ positive,Nat.and_two_pow_sub_one_eq_mod]
  calc
    _ = (n &&& ((2^k-1)*2^shift))%2^shift +
        (n &&& ((2^k-1)*2^shift))/2^shift*2^shift := by
          simpa only [Nat.mul_comm] using (Nat.mod_add_div (n &&& ((2^k-1)*2^shift)) (2^shift)).symm
    _ = _ := by rw [low,high,Nat.zero_add]

/-- Under the checked no-hardirq guards, a second BH-disable cannot
introduce a new instrumentation gate. This keeps the existing conditional
metadata footprint sufficient for the nested phase. -/
theorem nested_masks (old : BitVec 32)
    (first : old &&& 0x000f0000=0) (second : (old+512) &&& 0x000f0000=0) :
    (old+512) &&& 0xff0000=old &&& 0xff0000 ∧
      (old+512) &&& 0x100=old &&& 0x100 := by
  have firstNat := congrArg BitVec.toNat first
  have secondNat := congrArg BitVec.toNat second
  clear first second
  change old.toNat &&& ((2^4-1)*2^16)=0 at firstNat
  change ((old.toNat+512)%4294967296) &&& ((2^4-1)*2^16)=0 at secondNat
  rw [shifted_mask] at firstNat secondNat
  change old.toNat/65536%16*65536=0 at firstNat
  change ((old.toNat+512)%4294967296)/65536%16*65536=0 at secondNat
  rw [show 4294967296=65536*65536 from rfl,Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 65536)] at secondNat
  have sameBlock : (old.toNat+512)/65536=old.toNat/65536 := by omega
  constructor
  · apply BitVec.eq_of_toNat_eq
    change ((old.toNat+512)%4294967296) &&& ((2^8-1)*2^16)=old.toNat &&& ((2^8-1)*2^16)
    rw [shifted_mask,shifted_mask]
    change ((old.toNat+512)%4294967296)/65536%256*65536=old.toNat/65536%256*65536
    rw [show 4294967296=65536*65536 from rfl,Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 65536),sameBlock]
  · apply BitVec.eq_of_toNat_eq
    change ((old.toNat+512)%4294967296) &&& ((2^1-1)*2^8)=old.toNat &&& ((2^1-1)*2^8)
    rw [shifted_mask,shifted_mask]
    change ((old.toNat+512)%4294967296)/256%2*256=old.toNat/256%2*256
    rw [show 4294967296=256*16777216 from rfl,Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16777216)]
    clear firstNat secondNat sameBlock
    omega

#print axioms nested_masks

theorem nested_gate (coverage : KcovLayout) (old : BitVec 32)
    (first : old &&& 0x000f0000=0) (second : (old+512) &&& 0x000f0000=0) :
    LookupSoftRead (old+512)=LookupSoftRead old ∧
      LookupModeRead coverage (old+512)=LookupModeRead coverage old := by
  obtain ⟨high,low⟩ := nested_masks old first second
  have combined : (old+512) &&& 0xff0100=old &&& 0xff0100 := by
    change (old+512) &&& (0xff0000 ||| 0x100)=old &&& (0xff0000 ||| 0x100)
    rw [BitVec.and_or_distrib_left,BitVec.and_or_distrib_left,high,low]
  simp only [LookupSoftRead,LookupModeRead,combined,high,low,and_self]

theorem nested_coverage (c : Context)
    (first : (c.preempt+512) &&& 0x000f0000=0)
    (second : (c.preempt+1024) &&& 0x000f0000=0) (memory : DataMem) :
    (Context.mk c.coverage (c.preempt+1024)).CoverageAt memory=
      (Context.mk c.coverage (c.preempt+512)).CoverageAt memory := by
  have add : c.preempt+512+512=c.preempt+1024 := by rw [BitVec.add_assoc]; rfl
  have gates := nested_gate c.coverage (c.preempt+512) first (by rw [add]; exact second)
  rw [add] at gates
  simp only [Context.CoverageAt,Context.Needed,gates.1,gates.2]

theorem nested_bytes (c : Context)
    (first : (c.preempt+512) &&& 0x000f0000=0)
    (second : (c.preempt+1024) &&& 0x000f0000=0) (address : BitVec 64) :
    (Context.mk c.coverage (c.preempt+1024)).bytes address=
      (Context.mk c.coverage (c.preempt+512)).bytes address := by
  have add : c.preempt+512+512=c.preempt+1024 := by rw [BitVec.add_assoc]; rfl
  have gates := nested_gate c.coverage (c.preempt+512) first (by rw [add]; exact second)
  rw [add] at gates
  simp only [Context.bytes,Context.metadataBytes,Context.Needed,gates.1,gates.2]

#print axioms nested_coverage
#print axioms nested_bytes
end Binary.Pair.Insert
