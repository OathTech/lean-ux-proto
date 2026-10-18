import PairInsertWalk
import PairInsertNestedRegion

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Index

theorem u64_address {v : UInt64} {base : Nat} (equal : v.toNat=base) :
    v.toBitVec=BitVec.ofNat 64 base := by
  subst base
  apply BitVec.eq_of_toNat_eq
  simp only [UInt64.toNat_toBitVec,BitVec.toNat_ofNat,Nat.mod_eq_of_lt v.toNat_lt_size]

theorem Core.owner_address {n o c initial ra p shadow s base}
    (core : Core n o c initial ra p shadow s) (argument : initial.data.regs.rsi.toNat=base) :
    s.regs.rbp.toBitVec=BitVec.ofNat 64 base := by
  rw [core.owner]
  exact u64_address argument

theorem Core.table_address {n o c initial ra p shadow s}
    (core : Core n o c initial ra p shadow s) (argument : initial.data.regs.rdi.toNat=n.table) :
    s.regs.r12.toBitVec=BitVec.ofNat 64 n.table := by
  rw [core.table]
  exact u64_address argument

theorem mask_index (index : Nat) :
    ((BitVec.ofNat 32 index &&& 8191).setWidth 64).toNat=index%8192 := by
  have mask : (BitVec.ofNat 32 index &&& 8191).toNat=index%8192 := by
    change (index%2^32) &&& (2^13-1)=index%2^13
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_mod_of_dvd index (by decide)
  rw [BitVec.toNat_setWidth,mask]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt index (by decide : 0<8192); omega)

theorem Core.bucket_address {n o c initial ra p shadow s index}
    (core : Core n o c initial ra p shadow s) (layout : Layout o)
    (argument : initial.data.regs.rdi.toNat=n.table) :
    nestedBucketAddress s (.ofNat 32 index)=BitVec.ofNat 64 (tableHead n o (index%8192)) := by
  have masked : (BitVec.ofNat 32 index &&& 8191).setWidth 64=BitVec.ofNat 64 (index%8192) := by
    apply BitVec.eq_of_toNat_eq
    exact (mask_index index).trans (Nat.mod_eq_of_lt (by
      have := Nat.mod_lt index (by decide : 0<8192); omega)).symm
  rw [nestedBucketAddress,core.table_address argument,masked]
  simp only [tableHead,layout.buckets,layout.headSize,layout.first,Nat.add_zero,
    BitVec.ofNat_add,BitVec.ofNat_mul]
  rfl

/-- A second disable changes only the preempt word; the protected heap
and all saved/callback resources are framed through the update. -/
theorem Core.nested_memory {n o c initial ra shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .outer shadow s) :
    Core n o c initial ra .inner shadow {s with dmem := Remove.preemptMemory s (c.preempt+512)} := by
  have frame := storeInt_frame s.dmem preemptCountAddress 4
    (BitVec.ofInt 32 (512+(c.preempt+512).toNat)).toInt
  have count := Remove.preempt_read s (c.preempt+512)
  have next : load32 (Remove.preemptMemory s (c.preempt+512)) preemptCountAddress=
      some (Phase.inner.context c).preempt := by
    rw [count]
    change some (c.preempt+512+512)=some (c.preempt+1024)
    rw [BitVec.add_assoc]
    rfl
  refine ⟨core.stack,core.table,core.owner,core.memory.preempt_transition facts frame next,?_⟩
  apply core.frame.trans
  apply external_storage facts.toCallFacts.geometry
  intro a outside
  exact frame a (fun inside => outside (.inr (.inr inside)))

#print axioms Core.nested_memory
end Binary.Pair.Insert
