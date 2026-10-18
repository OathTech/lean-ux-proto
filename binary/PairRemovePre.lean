import PairIndexAssert
import PairIndexGeometry

namespace Binary.Pair.Remove
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

def Pre (n : Names) (o : Offsets) (c : Context) (s : MachineState)
    (w : World) (owner : IndexOwner) (ra : UInt64) : Prop := callBoundary n o c s w owner ra=.ok ()

theorem addressOf_ok {n : Names} {owner : IndexOwner} {base : Nat}
    (read : addressOf n owner=.ok base) : (owner,base) ∈ n.owners := by
  unfold addressOf at read
  cases found : n.owners.find? (·.1==owner) with
  | none => rw [found] at read; cases read
  | some pair =>
    rw [found] at read
    have eq : pair.2=base := Except.ok.inj read
    have ownerCheck : (pair.1==owner)=true := List.find?_some (p := fun x : IndexOwner × Nat => x.1==owner) found
    have ownerEq : pair.1=owner := eq_of_beq ownerCheck
    have member := List.mem_of_find?_eq_some found
    simpa only [←eq,←ownerEq] using member

theorem pre_facts {n o c s w owner ra} (pre : Pre n o c s w owner ra) :
    ∃ d base, w.k.wg=some d ∧ Corresponds n o s.data.dmem d ∧ storageCheck n o=true ∧
      ownership n o s.data.dmem=.ok (targetOwnership d) ∧ (owner,base) ∈ n.owners ∧
      s.pc.toBitVec.toNat=entry ∧ s.data.regs.rsi.toNat=base ∧ CallFacts n o c s ra 4 := by
  unfold Pre callBoundary at pre
  obtain ⟨_,checked,pre⟩ := bind_ok pre
  obtain ⟨d,device,related,storage,owners⟩ := remove_assert_ok checked
  obtain ⟨base,named,pre⟩ := bind_ok pre
  obtain ⟨arguments,ready⟩ := check_ok _ _ _ _ pre
  have args : s.pc.toBitVec.toNat=entry ∧ s.data.regs.rsi.toNat=base := by
    simpa only [Bool.and_eq_true,beq_iff_eq] using arguments
  exact ⟨d,base,device,related,storage,owners,addressOf_ok named,args.1,args.2,callFrameCheck_sound ready⟩

/-- The runtime ownership check relates the branch word even when no bucket
contains this entry. It therefore covers repeated removal without reading
the absent entry's unused next pointer. -/
theorem ownership_flag {n o m d owner base}
    (related : ownership n o m=.ok (targetOwnership d)) (named : (owner,base) ∈ n.owners) :
    ∃ previous, word m "owner.pprev" (base+o.hash+o.pprev) 8=.ok previous ∧
      (previous != 0 : Bool)=d.indexTable.any (·.owner==owner) := by
  obtain ⟨result,member,decoded⟩ := (mapM_ok related).left (owner,base) named
  obtain ⟨previous,read,done⟩ := bind_ok decoded
  have resultEq : (owner,(previous != 0 : Bool))=result := Except.ok.inj done
  rw [←resultEq] at member
  obtain ⟨other,_,equal⟩ := List.mem_map.mp member
  have ownerEq : other=owner := congrArg Prod.fst equal
  subst other
  exact ⟨previous,read,congrArg Prod.snd equal |>.symm⟩

#print axioms pre_facts
#print axioms ownership_flag

theorem pre_of_parts {n o c s w owner ra base}
    (asserted : assertAt n o s.data.dmem w=.ok ())
    (address : addressOf n owner=.ok base)
    (arguments : (s.pc.toBitVec.toNat==entry && s.data.regs.rsi.toNat==base)=true)
    (frame : Index.callFrameCheck n o c s ra 4=.ok ()) : Pre n o c s w owner ra := by
  unfold Pre callBoundary
  rw [asserted,address]
  change (if s.pc.toBitVec.toNat==entry && s.data.regs.rsi.toNat==base then
    Index.callFrameCheck n o c s ra 4 else Except.error "remove.call.entry-arguments")=.ok ()
  rw [arguments]
  exact frame
end Binary.Pair.Remove
