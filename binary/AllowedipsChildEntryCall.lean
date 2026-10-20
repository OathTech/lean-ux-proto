import AllowedipsChildSaveCall
import AllowedipsRootTotalMemory

namespace Binary.Pair.Allowedips.ChildFinish
open Root CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- Saving the allocation and the earlier PC callback establish selection's
actual saved input, pending resources and frame. -/
theorem entry_call (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch)
    {names entry d key cidr pid base s} (c : Context)
    (ready : CallsReady c s)
    (pending : NodeInit.Pending names entry d key cidr pid base s.dmem)
    (allocation : s.regs.r8.toNat=base) (parent : s.regs.rbx≠0)
    (extent : s.regs.rsp.toNat+32≤2^64)
    (mapped : (s.dmem.loadInt (.ofNat 64 (s.regs.rsp.toNat+24)) 8).isSome=true)
    (contextApart : ∀ a, c.bytes a → ¬ChildSetup.Writes s.regs.rsp a)
    (savedApart : ∀ a, ChildSetup.Writes s.regs.rsp a → ¬CallWrites s.regs.rsp c a)
    (projectionApart : ∀ span ∈ readSpans (names.allocated base) nodeOffsets,
      ∀ a, span.contains a → ¬SetupWrites s.regs.rsp c a)
    (tableApart : ∀ a, InRange (.ofNat 64 names.table) 24 a → ¬SetupWrites s.regs.rsp c a) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x212 ∧ t.data.regs.rsp=s.regs.rsp ∧ t.data.regs.rbx=s.regs.rbx ∧
      t.data.regs.r13=s.regs.r13 ∧ CallsReady c t.data ∧
      EqualOutside (SetupWrites s.regs.rsp c) s.dmem t.data.dmem ∧
      NodeInit.Pending names entry d key cidr pid base t.data.dmem ∧
      word t.data.dmem "saved.base" (s.regs.rsp.toNat+24) 8=.ok base ∧
      ∀ address size, (s.dmem.loadInt address size).isSome=true →
        (∀ a, InRange address size a → ¬CallWrites s.regs.rsp c a) →
        (t.data.dmem.loadInt address size).isSome=true)
      ⟨s,Add.entry+0x1ff⟩ := by
  let memory := s.dmem.storeInt (.ofNat 64 (s.regs.rsp.toNat+24)) 8 s.regs.r8.toNat
  have store := store_total (value:=s.regs.r8.toNat) mapped
  have checked : ChildSetup.entryEffect s=.ok (memory,0x20d) := by
    simp only [ChildSetup.entryEffect,store,beq_iff_eq,parent,ite_false]
    rfl
  have saved : word memory "saved.base" (s.regs.rsp.toNat+24) 8=.ok base := by
    rw [←allocation]
    exact word_store_same _ _ _ _ _ extent s.regs.r8.toBitVec.isLt
  apply eventually_trans (instructionStep fetch) _ _ _ (ChildSetup.entry_checked fetch decoder checked)
  rintro a ⟨pcA,regsA,memA,frameA,mappedA⟩
  have readyA : CallsReady c a.data := ready.frame (by rw [regsA]) frameA mappedA contextApart
  have here := decoder.add _ _ (show Add.fetch (Add.entry+0x20d)=some _ from rfl)
  rw [Placement.at_pc a _ pcA]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Services.call fetch (Add.entry+0x20d) "L_ffffffff810f31f0" .pc tracePc here c a.data readyA)
  rintro t ⟨pc,stack,bx,_,_,query,_,_,readyT,frameT⟩
  rw [regsA] at stack bx query frameT
  have combined : EqualOutside (SetupWrites s.regs.rsp c) s.dmem t.data.dmem := by
    intro address outside
    exact (frameA address (fun h => outside (.inl h))).trans
      (frameT address (fun h => outside (.inr h)))
  refine ⟨pc,stack,bx,query,readyT,combined,pending.frame combined projectionApart tableApart,?_,?_⟩
  · apply Eq.trans (Trie.word_frame frameT _ _ _ _).symm
      (show word a.data.dmem "saved.base" (s.regs.rsp.toNat+24) 8=.ok base from memA ▸ saved)
    rintro address ⟨i,bound,location⟩
    apply savedApart address
    refine ⟨24+i,by omega,?_⟩
    simpa only [BitVec.ofNat_add,ofNat_uint64,BitVec.add_assoc] using location
  · intro address size mapped apart
    rw [←frameT.loadInt address size (fun i hi => apart _ ⟨i,hi,rfl⟩)]
    exact mappedA _ _ mapped

#print axioms entry_call
end Binary.Pair.Allowedips.ChildFinish
