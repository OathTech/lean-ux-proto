import CommonBitsTrace
import AllowedipsEntryStack
import AllowedipsLoopObservation
import AllowedipsLayoutProofs

namespace Binary.AllowedipsOuterTrace
open CommonBits TrustBase AllowedipsLoop
local instance : Labels := Image.linkedLabels

theorem quiet_write (fetch : Int64 → Option Decoded) (pc : Int64)
    (code : List (Kraken.Sized Directive)) (layout : LaidOut fetch pc code)
    (s : MachineData) (P : MachineState → Prop) (writes : BitVec 64 → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d,p⟩)).All
      (fun t => P t ∧ EqualOutside writes s.dmem t.data.dmem))
    (rxSection : Nat)
    (silent : ∀ address ∈ AllowedipsLoop.regionPCs pc code, ∀ before after,
      before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [])
    (noInterior : ∀ address ∈ (AllowedipsLoop.regionPCs pc code).tail,
      ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints))
    (ordinary : ∀ address ∈ AllowedipsLoop.regionPCs pc code,
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a) :
    Eventually (historyStep fetch) (fun t => P t.machine ∧ Local writes ⟨s,pc⟩ rxSection [] t)
      ⟨⟨s,pc⟩,[⟨s,pc⟩]⟩ := by
  have executed := AllowedipsLoop.region_history layout s _ run []
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨⟨post,frame⟩,path,head,last,recorded,inside⟩
  have eq : t.history = path := by simpa only [List.nil_append] using recorded
  refine ⟨post, ?_⟩
  refine ⟨by rw [eq]; exact head, by rw [eq]; exact last, ?_, frame, ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    rw [eq]
    apply AllowedipsLoop.observe_silent
    intro before member after
    exact silent before.pc (inside before member).1 before after rfl
  · intro q member cut
    rw [eq, ← AllowedipsLoop.history_restore last] at member
    rcases List.mem_append.mp member with prior | endpoint
    · rcases (inside q prior).2 with start | interior
      · rw [start]; intro _ _; rfl
      · exact False.elim (noInterior q.pc interior cut)
    · have same : q = t.machine := List.mem_singleton.mp endpoint
      simpa only [same] using frame
  · intro q member
    rw [eq] at member
    exact ordinary q.pc (inside q member).1

theorem prologue_prefix (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (s : MachineData)
    (stack : ∀ i<7, (s.dmem.loadInt (Allowedips.entrySlot s i) 8).isSome = true)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = {s.regs with
        r12 := .ofBitVec ((s.regs.get (.low .rsi .W32)).setWidth 64),
        rbx := .ofBitVec ((s.regs.get (.low .rsi .W32)).setWidth 64),
        rbp := s.regs.rdx, rsp := s.regs.rsp-80} ∧
       t.machine.data.dmem = Allowedips.entryMemory s 7 ∧
       t.machine.pc = AllowedipsImage.Lookup.entry+0x1b) ∧
      Local (InRange (s.regs.rsp.toBitVec-88) 88) ⟨s,AllowedipsImage.Lookup.entry⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry⟩,[⟨s,AllowedipsImage.Lookup.entry⟩]⟩ := by
  have layout := (AllowedipsLoop.layout_take AllowedipsLookup.r00_layout 11).agreement agree
  simp only [Int64.add_zero] at layout
  have static : ∀ address ∈ regionPCs AllowedipsImage.Lookup.entry (AllowedipsImage.Lookup.r00.take 11),
      Quiet address ∧ address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a := by
    intro address member
    change address ∈ [AllowedipsImage.Lookup.entry,AllowedipsImage.Lookup.entry+2,
      AllowedipsImage.Lookup.entry+4,AllowedipsImage.Lookup.entry+6,AllowedipsImage.Lookup.entry+8,
      AllowedipsImage.Lookup.entry+11,AllowedipsImage.Lookup.entry+12,AllowedipsImage.Lookup.entry+15,
      AllowedipsImage.Lookup.entry+16,AllowedipsImage.Lookup.entry+18,AllowedipsImage.Lookup.entry+22] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      unfold Quiet <;> decide
  apply quiet_write fetch _ _ layout s (fun t =>
      t.data.regs = {s.regs with
        r12 := .ofBitVec ((s.regs.get (.low .rsi .W32)).setWidth 64),
        rbx := .ofBitVec ((s.regs.get (.low .rsi .W32)).setWidth 64),
        rbp := s.regs.rdx, rsp := s.regs.rsp-80} ∧
      t.data.dmem = Allowedips.entryMemory s 7 ∧ t.pc = AllowedipsImage.Lookup.entry+0x1b)
    (InRange (s.regs.rsp.toBitVec-88) 88) ?_ rxSection
    (fun address member before after eq => quiet_edge rxSection before after (eq ▸ (static address member).1))
    ?_ (fun address member => (static address member).2)
  · exact all_mono _ _ _ (fun t h => ⟨h, by rw [h.2.1]; exact Allowedips.entryMemory_frame s 7 (by decide)⟩)
      (Allowedips.prologuePrefix s stack)
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+2,AllowedipsImage.Lookup.entry+4,
      AllowedipsImage.Lookup.entry+6,AllowedipsImage.Lookup.entry+8,AllowedipsImage.Lookup.entry+11,
      AllowedipsImage.Lookup.entry+12,AllowedipsImage.Lookup.entry+15,AllowedipsImage.Lookup.entry+16,
      AllowedipsImage.Lookup.entry+18,AllowedipsImage.Lookup.entry+22] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

#print axioms prologue_prefix
end Binary.AllowedipsOuterTrace
