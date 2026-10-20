import AllowedipsReturnChecked
import PairServiceCall
import PairAllowedipsHeapFrame

namespace Binary.Pair.Allowedips.Return
open AllowedipsMutationImage CommonBitsCoverage
local instance : Labels := Image.linkedLabels

def Writes (s : MachineData) (c : Context) (a : BitVec 64) : Prop :=
  InRange (s.regs.rsp.toBitVec-8) 8 a ∨ c.writes a

theorem saved_congr {s t : MachineData} {writes offset}
    (stack : t.regs.rsp=s.regs.rsp) (frame : EqualOutside writes s.dmem t.dmem)
    (apart : ∀ a, InRange (s.regs.rsp.toBitVec+.ofNat 64 offset) 8 a → ¬writes a) :
    saved s offset=saved t offset := by
  have same := frame.loadBytes (s.regs.rsp.toBitVec+.ofNat 64 offset) 8
    (fun i hi => apart _ ⟨i,hi,rfl⟩)
  simp only [saved,readNat,stack,BitVec.ofNat_toNat,BitVec.setWidth_eq,same]

theorem addEffect_frame {s t : MachineData} {writes regs pc}
    (stack : t.regs.rsp=s.regs.rsp) (result : t.regs.rbx=s.regs.rbx)
    (frame : EqualOutside writes s.dmem t.dmem)
    (apart : ∀ offset ∈ [48,56,64,72,80,88,96], ∀ a,
      InRange (s.regs.rsp.toBitVec+.ofNat 64 offset) 8 a → ¬writes a)
    (checked : addEffect s=.ok (regs,pc)) :
    ∃ regs', addEffect t=.ok (regs',pc) ∧ observed regs'=observed regs := by
  unfold addEffect at checked ⊢
  obtain ⟨bx,h0,checked⟩ := bind_ok checked
  obtain ⟨bp,h1,checked⟩ := bind_ok checked
  obtain ⟨r12,h2,checked⟩ := bind_ok checked
  obtain ⟨r13,h3,checked⟩ := bind_ok checked
  obtain ⟨r14,h4,checked⟩ := bind_ok checked
  obtain ⟨r15,h5,checked⟩ := bind_ok checked
  obtain ⟨ra,h6,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have same (offset) (member : offset ∈ [48,56,64,72,80,88,96]) :=
    saved_congr stack frame (apart offset member)
  rw [←same 48 (by simp),←same 56 (by simp),←same 64 (by simp),
    ←same 72 (by simp),←same 80 (by simp),←same 88 (by simp),←same 96 (by simp)]
  simp only [h0,h1,h2,h3,h4,h5,h6]
  refine ⟨_,rfl,?_⟩
  simp only [observed,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,result,stack]

/-- The final actual coverage call and the epilogue preserve the completed
mutation's projection. Saved words and separation are current-state resources,
not assumptions about a future execution. -/
theorem finish_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch)
    {names o d s regs pc} (c : Context)
    (ready : CallsReady c s)
    (checked : addEffect s=.ok (regs,pc))
    (savedApart : ∀ offset ∈ [48,56,64,72,80,88,96], ∀ a,
      InRange (s.regs.rsp.toBitVec+.ofNat 64 offset) 8 a → ¬Writes s c a)
    (related : Corresponds names o s.dmem d)
    (shape : heap names (target d) s.dmem=.ok ())
    (projectionApart : ∀ span ∈ readSpans names o, ∀ a, span.contains a → ¬Writes s c a) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=pc ∧ observed t.data.regs=observed regs ∧ c.At t.data.dmem ∧
      EqualOutside (Writes s c) s.dmem t.data.dmem ∧
      Corresponds names o t.data.dmem d ∧ heap names (target d) t.data.dmem=.ok ())
      ⟨s,Add.entry+0x549⟩ := by
  have here := decoder.add _ _ (show Add.fetch (Add.entry+0x549)=some _ from rfl)
  have call := Services.call fetch (Add.entry+0x549) "L_ffffffff810f31f0" .pc tracePc here c s ready
  apply eventually_trans (instructionStep fetch) _ _ _ call
  rintro a ⟨pcA,stack,bx,_,_,_,_,_,readyA,frame⟩
  obtain ⟨regs',checked',observed'⟩ := addEffect_frame stack bx frame savedApart checked
  have relatedA : Corresponds names o a.data.dmem d :=
    (reconstruct_frame names o frame projectionApart).symm.trans related
  have metadataApart : ∀ span ∈ metadataSpans names o, ∀ a, span.contains a → ¬Writes s c a := by
    intro span member
    apply projectionApart span
    simp only [metadataSpans,readSpans,List.mem_append] at member ⊢
    rcases member with table | node | peer
    · exact .inl table
    · exact .inr (.inl node)
    · apply Or.inr ∘ Or.inr
      obtain ⟨pair,named,field⟩ := List.mem_flatMap.mp peer
      obtain ⟨slot,present,equal⟩ := List.mem_map.mp field
      exact List.mem_flatMap.mpr ⟨pair,named,List.mem_map.mpr
        ⟨slot,List.mem_cons_of_mem _ present,equal⟩⟩
  have shapeA := (heap_frame names o (target d) frame metadataApart).symm.trans shape
  have position : a.pc=Add.entry+0x54e := pcA
  rw [Placement.at_pc a _ position]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (add_checked fetch decoder checked')
  rintro t ⟨registers,memory,pc⟩
  exact ⟨pc,registers ▸ observed',memory.symm ▸ readyA.state,
    memory.symm ▸ frame,memory.symm ▸ relatedA,memory.symm ▸ shapeA⟩

#print axioms finish_checked
end Binary.Pair.Allowedips.Return
