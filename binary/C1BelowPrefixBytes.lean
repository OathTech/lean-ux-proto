import C1BelowPrefixFinal

/-! Result C1, work package 3, prefix: the three selector bytes the first
initialization leaves on the stack (`rsp+0x24`, `+0x2b`, `+0x2c`), read later
by the covering path (`add+0x57b`, `+0x580`) and the internal node's
initialization (`add+0x2dd`), and their survival to `add+0x267`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root
local instance : Labels := Image.linkedLabels

theorem load_store_byte (m : DataMem) (address : BitVec 64) (value : Nat) (bound : value<256) :
    (m.storeInt address 1 (value : Int)).loadInt address 1=some (value : Int) := by
  have read := MemoryBytes.loadInt_store_subword m address 1 (value : Int) (by decide) 0 1 (by decide)
  have reduce : (value : Int)%256=(value : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  simpa [reduce] using read

/-- A byte store at another stack offset keeps a stack byte. -/
theorem byte_kept (m : DataMem) (stack : UInt64) (extent : stack.toNat+48≤2^64) (kept written : Nat)
    (different : kept≠written) (keptBound : kept<48) (writtenBound : written<48) (value : Int) :
    (m.storeInt (.ofNat 64 (stack.toNat+written)) 1 value).loadInt (stack.toBitVec+.ofNat 64 kept) 1=
      m.loadInt (stack.toBitVec+.ofNat 64 kept) 1 := by
  symm
  apply (storeInt_frame m _ 1 value).loadInt
  rintro i bound ⟨j,boundJ,location⟩
  rw [slot_address] at location
  have rsp : stack.toBitVec.toNat=stack.toNat := rfl
  have top : stack.toNat+48≤2^64 := extent
  bv_omega

/-- The selector bytes in the memory the first initialization leaves. -/
theorem init_bytes {names : Allowedips.Names} {world : World} {e : MachineState}
    {key cidr pid base : Nat} {c : Context} {m : DataMem}
    (fields : NodeInit.BoundaryFields names nodeOffsets world e key cidr pid base)
    (res : Res names c e.data base)
    (summary : NodeInit.effect e.data=.ok (m,base)) :
    m.loadInt (e.data.regs.rsp.toBitVec+0x24) 1=some (((e.data.regs.rbp.toNat/8-1)%8 : Nat) : Int) ∧
    m.loadInt (e.data.regs.rsp.toBitVec+0x2b) 1=
      some (((cidr/8) ^^^ ((e.data.regs.rbp.toNat/8-1)%8) : Nat) : Int) ∧
    m.loadInt (e.data.regs.rsp.toBitVec+0x2c) 1=some ((7-cidr%8 : Nat) : Int) := by
  obtain ⟨attached,initialized,attachment,headerCheck,copyCheck⟩ := NodeInit.effect_parts fields.original summary
  have extent := res.extent
  have cidrBound := fields.cidrBound
  have family := fields.family
  have maskBound : (e.data.regs.rbp.toNat/8-1)%8<8 := Nat.mod_lt _ (by decide)
  have xorBound : (cidr/8) ^^^ ((e.data.regs.rbp.toNat/8-1)%8)<256 := by
    have small : (cidr/8) ^^^ ((e.data.regs.rbp.toNat/8-1)%8)<2^5 :=
      Nat.xor_lt_two_pow (by rcases family with h|h <;> omega) (by omega)
    omega
  have tail : EqualOutside (InRange (.ofNat 64 base) 72) initialized m := by
    have copied := copy_frame copyCheck
    have baseNat : (UInt64.ofNat base).toNat=base := by
      have fresh := (allocated_facts fields.allocated).2.2.1
      change base+72<2^64 at fresh
      exact Nat.mod_eq_of_lt (by omega)
    simp only [baseNat] at copied
    intro a outside
    exact copied a (fun ⟨i,bound,location⟩ => outside ⟨i,by omega,location⟩)
  unfold NodeInit.header at headerCheck
  obtain ⟨m1,first,headerCheck⟩ := bind_ok headerCheck
  obtain ⟨m2,second,headerCheck⟩ := bind_ok headerCheck
  obtain ⟨m3,third,last⟩ := bind_ok headerCheck
  have m1Eq := (store_facts first).2
  have m2Eq := (store_facts second).2
  have m3Eq := (store_facts third).2
  have lastEq := (store_facts last).2
  have record : EqualOutside (InRange (.ofNat 64 base) 72) m3 m := by
    intro a outside
    refine Eq.trans ?_ (tail a outside)
    rw [lastEq]
    apply storeInt_frame _ _ _ _ a
    rintro ⟨i,bound,location⟩
    apply outside
    refine ⟨24+i,by omega,?_⟩
    rw [location]
    bv_omega
  have stackByte (offset : Nat) (member : offset ∈ [36,43,44]) :
      m.loadInt (e.data.regs.rsp.toBitVec+.ofNat 64 offset) 1=
        m3.loadInt (e.data.regs.rsp.toBitVec+.ofNat 64 offset) 1 := by
    symm
    apply record.loadInt
    intro i bound inside
    apply fields.stack_node_apart _ inside
    refine ⟨offset,member,i,bound,?_⟩
    rw [slot_address]
  refine ⟨?_,?_,?_⟩
  · rw [show (0x24 : BitVec 64)=BitVec.ofNat 64 36 from rfl,stackByte 36 (by decide),m3Eq,m2Eq,m1Eq,
      byte_kept _ _ extent 36 44 (by decide) (by decide) (by decide),
      byte_kept _ _ extent 36 43 (by decide) (by decide) (by decide),slot_address]
    exact load_store_byte _ _ _ (by omega)
  · rw [show (0x2b : BitVec 64)=BitVec.ofNat 64 43 from rfl,stackByte 43 (by decide),m3Eq,m2Eq,
      byte_kept _ _ extent 43 44 (by decide) (by decide) (by decide),slot_address]
    exact load_store_byte _ _ _ xorBound
  · rw [show (0x2c : BitVec 64)=BitVec.ofNat 64 44 from rfl,stackByte 44 (by decide),m3Eq,slot_address]
    exact load_store_byte _ _ _ (by omega)

/-- The selector bytes are not written after the first initialization. -/
theorem Held.selector_byte {names : Allowedips.Names} {c : Context} {e : MachineData} {d : Device}
    {key cidr pid base child : Nat} {m : DataMem} {t : MachineData}
    (held : Held names c e d key cidr pid base child m t) (res : Res names c e base)
    (offset : Nat) (above : 32≤offset) (within : offset<48) :
    t.dmem.loadInt (t.regs.rsp.toBitVec+.ofNat 64 offset) 1=
      m.loadInt (e.regs.rsp.toBitVec+.ofNat 64 offset) 1 := by
  rw [held.stack]
  symm
  apply held.late.loadInt
  rintro i bound (⟨j,boundJ,location⟩|⟨j,boundJ,location⟩|written)
  · bv_omega
  · bv_omega
  · exact res.context _ (writes_bytes written) (zone_local (by omega) ⟨i,bound,rfl⟩)

#print axioms init_bytes
#print axioms Held.selector_byte
end Binary.Statements.C1.Proof
