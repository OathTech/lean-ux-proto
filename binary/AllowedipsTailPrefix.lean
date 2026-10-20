import AllowedipsTailMemory
import AllowedipsEntryRegionTrace
import CommonBitsCallbackTrace
import CommonBitsEntryHistory

namespace Binary.AllowedipsTail
open TrustBase CommonBitsCoverage CommonBits AllowedipsEntry Instrumentation
local instance : Labels := Image.linkedLabels

structure Stored (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (ra result : UInt64) (s : MachineData) : Prop where
  ready : Ready initial coverage old ra s
  value : s.dmem.loadInt s.regs.rsp.toBitVec 8=some result.toNat

theorem store_trace (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (s : MachineData) (word : Int) (mapped : s.dmem.loadInt s.regs.rsp.toBitVec 8=some word)
    (rx : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs=s.regs ∧
       t.machine.data.dmem=s.dmem.storeInt s.regs.rsp.toBitVec 8 s.regs.rax.toBitVec.toInt ∧
       t.machine.pc=AllowedipsImage.Lookup.entry+0x126) ∧
      Local (InRange s.regs.rsp.toBitVec 8) ⟨s,AllowedipsImage.Lookup.entry+0x122⟩ rx [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x122⟩,[⟨s,AllowedipsImage.Lookup.entry+0x122⟩]⟩ := by
  apply AllowedipsEntry.quiet_region fetch _ _
    ((AllowedipsLoop.layout_take AllowedipsLookup.r122_layout 1).agreement agree) s
    (fun t => t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt s.regs.rsp.toBitVec 8 s.regs.rax.toBitVec.toInt ∧
      t.pc=AllowedipsImage.Lookup.entry+0x126) _ ?_ rx (by decide) (by decide)
  exact all_mono _ _ _ (fun t h => ⟨h,by rw [h.2.1]; exact storeInt_frame _ _ _ _⟩)
    (Allowedips.saveResult s word mapped)

theorem store_result (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (s : MachineData) (ready : Ready initial coverage old ra s) (rx : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x126 ∧ Stored initial coverage old ra s.regs.rax t.machine.data) ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x122⟩ rx [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x122⟩,[⟨s,AllowedipsImage.Lookup.entry+0x122⟩]⟩ := by
  obtain ⟨word,mapped⟩ := Option.isSome_iff_exists.mp ready.mappedResult
  apply eventually_weaken (historyStep fetch) _ _ _ _ (store_trace fetch agree s word mapped rx)
  rintro t ⟨⟨regs,memory,pc⟩,trace⟩
  refine ⟨⟨pc,ready.store_result pre regs memory,?_⟩,trace.mono ?_⟩
  · rw [regs,memory]; exact load64_store _ _ _
  · intro a member
    rw [ready.result_slot] at member
    exact .inl member

theorem pc_callback (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsTracePcContract fetch)
    {c coverage old ra initial world v result}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (s : MachineData) (stored : Stored initial coverage old ra result s) (rx : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x12b ∧ Stored initial coverage old ra result t.machine.data) ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x126⟩ rx [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x126⟩,[⟨s,AllowedipsImage.Lookup.entry+0x126⟩]⟩ := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x126)=
    some ⟨callInstruction "L_ffffffff810f31f0",5⟩ from rfl)
  have run := callback_trace fetch _ "L_ffffffff810f31f0" here .pc contract ⟨coverage,old+512⟩
    s stored.ready.calls rx (by intro after; rfl) (by decide)
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨⟨returned,calls⟩,trace⟩
  obtain ⟨pc,sp,bx,bp,r12,r13,r14,r15⟩ := returned_caller s _ _ t.machine returned
  have frame : EqualOutside (fun a => InRange (slot initial 11) 8 a ∨ (Context.mk coverage (old+512)).writes a)
      s.dmem t.machine.data.dmem := by simpa only [stored.ready.call_slot] using trace.frame
  have resultRead : t.machine.data.dmem.loadInt t.machine.data.regs.rsp.toBitVec 8=some result.toNat := by
    rw [sp,stored.ready.result_slot]
    exact (frame.loadInt _ 8 (fun i hi => callback_result_separate pre _ ⟨i,hi,rfl⟩)).symm.trans
      (by simpa only [stored.ready.result_slot] using stored.value)
  have localTrace := trace.mono (large := Writes initial coverage old) (fun a written => by
    rcases written with stack | buffer
    · exact Or.inr (Or.inl (by simpa only [stored.ready.call_slot] using stack))
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr buffer.1,buffer.2⟩)))
  refine ⟨⟨pc,?_,resultRead⟩,localTrace⟩
  exact stored.ready.advance pre sp calls (callback_before pre stored.ready.before calls.state.1 frame)
    (by rw [resultRead]; rfl) localTrace.frame

theorem before_enable (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsTracePcContract fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (s : MachineData) (ready : Ready initial coverage old ra s) (rx : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x12b ∧ Stored initial coverage old ra s.regs.rax t.machine.data) ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x122⟩ rx [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x122⟩,[⟨s,AllowedipsImage.Lookup.entry+0x122⟩]⟩ := by
  apply chain fetch _ _ rx [] []
    (fun t => t.pc=AllowedipsImage.Lookup.entry+0x126 ∧ Stored initial coverage old ra s.regs.rax t.data)
    (fun t => t.pc=AllowedipsImage.Lookup.entry+0x12b ∧ Stored initial coverage old ra s.regs.rax t.data)
    (store_result fetch agree pre s ready rx)
  rintro ⟨d,pc⟩ ⟨equal,stored⟩
  dsimp only at equal
  subst pc
  exact pc_callback fetch agree contract pre d stored rx

#print axioms before_enable
end Binary.AllowedipsTail
