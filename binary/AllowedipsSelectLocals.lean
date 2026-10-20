import AllowedipsSelectEmpty
import AllowedipsRootTotalMemory

namespace Binary.Pair.Allowedips.Select
open Root

/-- Registers retained by selection and the allocation loaded from its actual
saved word. Caller-saved values before the coverage call are not relied upon. -/
theorem effect_locals {s : MachineData} {memory : DataMem} {registers : Reg64s} {offset base : Nat}
    (saved : readNat ⟨s,0⟩ (s.regs.rsp.toNat+24) 8=.ok base)
    (checked : effect s=.ok (memory,registers,offset)) :
    registers.rsp=s.regs.rsp ∧ registers.rbx=s.regs.rbx ∧ registers.r8.toNat=base := by
  unfold effect at checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨actual,baseRead,checked⟩ := bind_ok checked
  have baseEq : actual=base := Except.ok.inj (baseRead.symm.trans saved)
  subst actual
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have bound := (loadInt_range _ _ _ _ (Trie.readNat_loadInt saved)).2
  change (base : Int)<18446744073709551616 at bound
  exact ⟨rfl,rfl,UInt64.toNat_ofNat_of_lt' (by change base<18446744073709551616; omega)⟩

end Binary.Pair.Allowedips.Select
