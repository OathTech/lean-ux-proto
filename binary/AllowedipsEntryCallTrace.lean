import AllowedipsEntryState

namespace Binary.AllowedipsEntry
open TrustBase CommonBitsCoverage CommonBits Instrumentation
local instance : Labels := Image.linkedLabels

/-- The actual entry callback CALL, whose return frame retains all physical
entry obligations. Only its scoped service contract is supplied. -/
theorem callback (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target,5⟩) (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch (label target)
      (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat)
    (silent : ∀ after, AllowedipsObservation.edge rxSection ⟨s,pc⟩ after = .ok [])
    (ordinary : pc ≠ Image.PeerGet.entry+0xaf ∧ pc ≠ Image.PeerGet.entry+0x4a) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=pc+5 ∧ At initial coverage old ra t.machine.data ∧
       EqualOutside (fun a => InRange (slot initial 11) 8 a ∨ (Context.mk coverage old).writes a)
         s.dmem t.machine.data.dmem) ∧
      Local (Writes initial coverage old) ⟨s,pc⟩ rxSection [] t)
      ⟨⟨s,pc⟩,[⟨s,pc⟩]⟩ := by
  have run := callback_trace fetch pc target here kind contract ⟨coverage,old⟩ s
    (state.ready pre) rxSection silent ordinary
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨⟨returned,ready⟩,trace⟩
  obtain ⟨atPC,sp,bx,bp,r12,r13,r14,r15⟩ := returned_caller s (pc+5) (label target) t.machine returned
  have frame : EqualOutside (fun a => InRange (slot initial 11) 8 a ∨ (Context.mk coverage old).writes a)
      s.dmem t.machine.data.dmem := by simpa only [call_slot state] using trace.frame
  have smallToLarge (a : BitVec 64) (member : InRange (s.regs.rsp.toBitVec-8) 8 a ∨
      (Context.mk coverage old).writes a) : Writes initial coverage old a := by
    rcases member with stack | buffer
    · rw [call_slot state] at stack
      exact .inl (slot_writes initial 11 (by decide) (by decide) a stack)
    · exact .inr buffer
  have localTrace := trace.mono smallToLarge
  refine ⟨⟨atPC,?_,frame⟩,localTrace⟩
  refine ⟨sp.trans state.stack,bx.trans state.bx,bp.trans state.bp,r12.trans state.r12,?_,?_⟩
  · apply memory_callback pre s.dmem t.machine.data.dmem state.memory ready.state _ frame
    simpa only [sp,call_slot state] using ready.mapped
  · intro a outside
    exact (state.frame a outside).trans (localTrace.frame a outside)

/-- Initial saves and the exact entry memory establish all reusable entry
state fields before the first callback. -/
theorem prologue (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x1b ∧ At initial coverage old ra t.machine.data) ∧
      Local (Writes initial coverage old) initial rxSection [] t)
      ⟨initial,[initial]⟩ := by
  have run := AllowedipsOuterTrace.prologue_prefix fetch agree initial.data
    (fun i hi => AllowedipsEntryContext.prologue_stack pre i (by omega)) rxSection
  have initialEq : (⟨initial.data,AllowedipsImage.Lookup.entry⟩ : MachineState)=initial := by
    cases initial; congr 1; exact pre.pc.symm
  rw [initialEq] at run
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨⟨registers,memory,pc⟩,trace⟩
  have localTrace := trace.mono (fun a written =>
    show Writes initial coverage old a from .inl (prologue_inside initial a written))
  refine ⟨⟨pc,?_,?_,?_,?_,?_,localTrace.frame⟩,localTrace⟩
  · simp only [registers]
  · simp only [registers]
  · simp only [registers]
  · simp only [registers]
  · rw [memory]; exact memory_prologue pre

#print axioms callback
#print axioms prologue
end Binary.AllowedipsEntry
