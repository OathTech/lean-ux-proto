import AllowedipsLoopScalar
import AllowedipsSetup

namespace Binary.AllowedipsOuter
open TrustBase AllowedipsLoop
local instance : Labels := Image.linkedLabels

private theorem scalar_trace {fetch pc code}
    (layout : LaidOut fetch pc code) (base s : MachineData)
    (coverage : CommonBitsCoverage.Context) (P : MachineState → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d,p⟩)).All
      (fun t => P t ∧ t.data.dmem = s.dmem ∧ t.data.regs.rsp = s.regs.rsp ∧
        t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13))
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,pc⟩)
    (static : ∀ address ∈ regionPCs pc code, Quiet address ∧
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a)
    (noInterior : ∀ address ∈ (regionPCs pc code).tail, ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints)) :
    Eventually (historyStep fetch) (fun t => P t.machine ∧ Trace base coverage rxSection history events t)
      ⟨⟨s,pc⟩,history⟩ := by
  apply quiet_trace layout base s coverage P ?_ frame rxSection history events observed last
    (fun address member before after eq => quiet_edge rxSection before after (eq ▸ (static address member).1))
    noInterior (fun address member => (static address member).2)
  exact all_mono _ _ _ (fun t h => ⟨h.1, frame.congr h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩) run

theorem root_load (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context) (value : BitVec 64)
    (field : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8 = some value.toNat)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x79⟩) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc = AllowedipsImage.Lookup.entry+0x7e ∧
       t.machine.data.regs = {s.regs with rbx := .ofBitVec value}) ∧
      Trace base coverage rxSection history events t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x79⟩,history⟩ := by
  refine scalar_trace ((AllowedipsLoop.layout_take AllowedipsLookup.r79_layout 1).agreement agree)
    base s coverage (fun t => t.pc = AllowedipsImage.Lookup.entry+0x7e ∧
      t.data.regs = {s.regs with rbx := .ofBitVec value}) ?_ frame rxSection history events observed last ?_ ?_
  · exact all_mono _ _ _ (fun t h => ⟨⟨h.2.2,h.1⟩,h.2.1,
      by rw [h.1],by rw [h.1],by rw [h.1]⟩) (Allowedips.rootLoad s value field)
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0x79] at member
    simp only [List.mem_singleton] at member
    subst address
    unfold Quiet
    decide
  · intro address member
    change address ∈ ([] : List Int64) at member
    cases member

 theorem clear_found (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x8c⟩) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc = AllowedipsImage.Lookup.entry+0xd5 ∧
       t.machine.data.regs = {s.regs with rbp := 0}) ∧
      Trace base coverage rxSection history events t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x8c⟩,history⟩ := by
  refine scalar_trace (AllowedipsLookup.r8c_layout.agreement agree)
    base s coverage (fun t => t.pc = AllowedipsImage.Lookup.entry+0xd5 ∧
      t.data.regs = {s.regs with rbp := 0}) ?_ frame rxSection history events observed last ?_ ?_
  · exact all_mono _ _ _ (fun t h => ⟨⟨h.2.2,h.1⟩,h.2.1,
      by rw [h.1],by rw [h.1],by rw [h.1]⟩) (Allowedips.clearFound s)
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0x8c,AllowedipsImage.Lookup.entry+0x8e] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> unfold Quiet <;> decide
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0x8e] at member
    simp only [List.mem_singleton] at member
    subst address
    decide

#print axioms root_load
#print axioms clear_found
end Binary.AllowedipsOuter
