import SourceAdapter
import PairInsertCallFacts
import PairInsertMemory

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index

structure Resident (n : Names) (o : Offsets) (m : DataMem) (owner : IndexOwner) (base : Nat) : Prop where
  named : (owner,base) ∈ n.owners
  kind : word m "insert.kind" (base+o.kind) 4=.ok (ownerKind owner)
  next : ∃ value, word m "insert.next" (base+o.hash+o.next) 8=.ok value
  index : ∃ value, word m "insert.index" (base+o.index) 4=.ok value

theorem boundary_data {n o c s w owner ra} (checked : callBoundary n o c s w owner ra=.ok ()) :
    ∃ d base, w.wg.dev=some d ∧ Corresponds n o s.data.dmem d ∧ storageCheck n o=true ∧
      Remove.ownership n o s.data.dmem=.ok (Remove.targetOwnership d) ∧
      Resident n o s.data.dmem owner base ∧
      s.pc.toBitVec.toNat=entry ∧ s.data.regs.rdi.toNat=n.table ∧ s.data.regs.rsi.toNat=base ∧
      FrameFacts n o c s ra := by
  have frame := boundary_frame checked
  unfold callBoundary at checked
  obtain ⟨_,asserted,checked⟩ := bind_ok checked
  obtain ⟨d,device,related,storage,owned⟩ := remove_assert_ok asserted
  obtain ⟨base,address,checked⟩ := bind_ok checked
  obtain ⟨arguments,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨kind,kindRead,checked⟩ := bind_ok checked
  obtain ⟨kindCheck,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨next,nextRead,checked⟩ := bind_ok checked
  obtain ⟨index,indexRead,_⟩ := bind_ok checked
  have args : s.pc.toBitVec.toNat=entry ∧ s.data.regs.rdi.toNat=n.table ∧ s.data.regs.rsi.toNat=base := by
    simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using arguments
  have kindEq : kind=ownerKind owner := eq_of_beq kindCheck
  refine ⟨d,base,device,related,storage,owned,⟨Remove.addressOf_ok address,?_,
    ⟨next,mapError_ok nextRead⟩,⟨index,mapError_ok indexRead⟩⟩,args.1,args.2.1,args.2.2,frame⟩
  rw [←kindEq]
  exact mapError_ok kindRead

#print axioms boundary_data
end Binary.Pair.Insert
