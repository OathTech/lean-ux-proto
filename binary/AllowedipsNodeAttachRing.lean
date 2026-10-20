import AllowedipsNodeAttachChecked
import AllowedipsRootAttachment
import PairStoreCommute

namespace Binary.Pair.Allowedips.NodeInit
open Root

/-- The nonempty path swaps the two fresh-node list stores relative to the
root path. They are disjoint offsets even when the allocation base wraps. -/
theorem attach_as_ring {s : MachineData} {memory base cidr}
    (checked : attach s=.ok (memory,base,cidr)) :
    ∃ last, readNat ⟨s,0⟩ (s.regs.r14.toNat+1104) 8=.ok last ∧
      memory=Ring.appendMemory (write64 s.dmem base s.regs.r14.toNat)
        (s.regs.r14.toNat+1096) last (base+56) := by
  unfold attach at checked
  obtain ⟨allocation,_,checked⟩ := bind_ok checked
  obtain ⟨requested,_,checked⟩ := bind_ok checked
  obtain ⟨last,tailRead,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨m1,ownerStore,checked⟩ := bind_ok checked
  obtain ⟨m2,headStore,checked⟩ := bind_ok checked
  obtain ⟨m3,backStore,checked⟩ := bind_ok checked
  obtain ⟨m4,forwardStore,checked⟩ := bind_ok checked
  obtain ⟨m5,lastStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have ownerEq := (store_facts ownerStore).2
  have headEq := (store_facts headStore).2
  have backEq := (store_facts backStore).2
  have forwardEq := (store_facts forwardStore).2
  have lastEq := (store_facts lastStore).2
  rw [store_nat64] at ownerEq headEq backEq forwardEq lastEq
  have reordered : m4=write64 (write64 m2 (base+56) (s.regs.r14.toNat+1096)) (base+64) last := by
    rw [forwardEq,backEq]
    exact write64_offsets_commute m2 base 64 56 last (s.regs.r14.toNat+1096)
      (by decide) (by decide) (.inr (by decide))
  refine ⟨last,tailRead,?_⟩
  simp only [lastEq,reordered,headEq,ownerEq,Ring.appendMemory,write64,Nat.add_assoc,Nat.reduceAdd]

#print axioms attach_as_ring
end Binary.Pair.Allowedips.NodeInit
