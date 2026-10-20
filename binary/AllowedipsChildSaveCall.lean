import AllowedipsChildSaved
import AllowedipsNodePendingFrame
import PairServiceCall

namespace Binary.Pair.Allowedips.ChildFinish
open Leanux Root CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def CallWrites (stack : UInt64) (c : Context) (a : BitVec 64) : Prop :=
  InRange (stack.toBitVec-8) 8 a ∨ c.writes a

def SetupWrites (stack : UInt64) (c : Context) (a : BitVec 64) : Prop :=
  ChildSetup.Writes stack a ∨ CallWrites stack c a

/-- The save instructions and the real PC callback preserve the pending heap
and produce publication's saved words. No future decoder success is a premise. -/
theorem save_call (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch)
    {names entry d key cidr pid base direction s memory} (c : Context)
    (ready : CallsReady c s)
    (pending : NodeInit.Pending names entry d key cidr pid base s.dmem)
    (allocation : s.regs.r8.toNat=base)
    (extent : s.regs.rsp.toNat+24≤2^64) (bit : direction<2)
    (index : s.regs.rax.toNat=direction) (byte : s.regs.rdx.toNat=direction)
    (checked : ChildSetup.saveEffect s=.ok memory)
    (contextApart : ∀ a, c.bytes a → ¬ChildSetup.Writes s.regs.rsp a)
    (savedApart : ∀ a, ChildSetup.Writes s.regs.rsp a → ¬CallWrites s.regs.rsp c a)
    (projectionApart : ∀ span ∈ readSpans (names.allocated base) nodeOffsets,
      ∀ a, span.contains a → ¬SetupWrites s.regs.rsp c a)
    (tableApart : ∀ a, InRange (.ofNat 64 names.table) 24 a → ¬SetupWrites s.regs.rsp c a) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x6f2 ∧ t.data.regs.rsp=s.regs.rsp ∧ t.data.regs.rbx=s.regs.rbx ∧
      CallsReady c t.data ∧ EqualOutside (SetupWrites s.regs.rsp c) s.dmem t.data.dmem ∧
      NodeInit.Pending names entry d key cidr pid base t.data.dmem ∧
      word t.data.dmem "saved.base" s.regs.rsp.toNat 8=.ok base ∧
      word t.data.dmem "saved.direction" (s.regs.rsp.toNat+8) 1=.ok direction ∧
      word t.data.dmem "saved.index" (s.regs.rsp.toNat+16) 8=.ok direction ∧
      ∀ address size, (s.dmem.loadInt address size).isSome=true →
        (∀ a, InRange address size a → ¬CallWrites s.regs.rsp c a) →
        (t.data.dmem.loadInt address size).isSome=true)
      ⟨s,Add.entry+0x6e0⟩ := by
  have saved := ChildSetup.save_words extent bit index byte checked
  rw [allocation] at saved
  apply eventually_trans (instructionStep fetch) _ _ _ (ChildSetup.save_checked fetch decoder checked)
  rintro a ⟨pcA,regsA,memA,frameA,mappedA⟩
  have readyA : CallsReady c a.data := ready.frame (by rw [regsA]) frameA mappedA contextApart
  have here := decoder.add _ _ (show Add.fetch (Add.entry+0x6ed)=some _ from rfl)
  rw [Placement.at_pc a _ pcA]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Services.call fetch (Add.entry+0x6ed) "L_ffffffff810f31f0" .pc tracePc here c a.data readyA)
  rintro t ⟨pc,stack,bx,_,_,_,_,_,readyT,frameT⟩
  rw [regsA] at stack bx frameT
  have combined : EqualOutside (SetupWrites s.regs.rsp c) s.dmem t.data.dmem := by
    intro address outside
    exact (frameA address (fun h => outside (.inl h))).trans
      (frameT address (fun h => outside (.inr h)))
  have pendingT := pending.frame combined projectionApart tableApart
  have savedAt (offset size : Nat) (within : offset+size≤32) (path : String) :
      word t.data.dmem path (s.regs.rsp.toNat+offset) size=
        word memory path (s.regs.rsp.toNat+offset) size := by
    rw [←memA]
    apply (Trie.word_frame frameT _ _ _ _).symm
    rintro address ⟨i,bound,location⟩
    apply savedApart address
    refine ⟨offset+i,by omega,?_⟩
    simpa only [BitVec.ofNat_add,ofNat_uint64,BitVec.add_assoc] using location
  refine ⟨pc,stack,bx,readyT,combined,pendingT,?_,?_,?_,?_⟩
  · simpa only [Nat.add_zero] using (savedAt 0 8 (by decide) "saved.base").trans saved.1
  · exact (savedAt 8 1 (by decide) "saved.direction").trans saved.2.1
  · exact (savedAt 16 8 (by decide) "saved.index").trans saved.2.2
  · intro address size mapped apart
    rw [←frameT.loadInt address size (fun i hi => apart _ ⟨i,hi,rfl⟩)]
    exact mappedA _ _ mapped

#print axioms save_call
end Binary.Pair.Allowedips.ChildFinish
