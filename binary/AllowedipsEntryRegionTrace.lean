import AllowedipsOuterTrace
import AllowedipsSetup
import AllowedipsEndian
import AllowedipsOuter

namespace Binary.AllowedipsEntry
open TrustBase CommonBits AllowedipsLoop
local instance : Labels := Image.linkedLabels
local instance (a : Int64) : Decidable (Quiet a) := by unfold Quiet; infer_instance

theorem quiet_region (fetch : Int64 → Option Decoded) (pc : Int64)
    (code : List (Kraken.Sized Directive)) (layout : LaidOut fetch pc code)
    (s : MachineData) (P : MachineState → Prop) (writes : BitVec 64 → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d,p⟩)).All
      (fun t => P t ∧ EqualOutside writes s.dmem t.data.dmem))
    (rxSection : Nat)
    (quiet : (regionPCs pc code).all (fun a => decide (Quiet a ∧
      a ≠ Image.PeerGet.entry+0xaf ∧ a ≠ Image.PeerGet.entry+0x4a)) = true)
    (interior : (regionPCs pc code).tail.all (fun a => decide (¬(a ∈ AllowedipsImage.cutPoints ∨ a ∈ Image.cutPoints))) = true) :
    Eventually (historyStep fetch) (fun t => P t.machine ∧ Local writes ⟨s,pc⟩ rxSection [] t)
      ⟨⟨s,pc⟩,[⟨s,pc⟩]⟩ := by
  have static : ∀ a ∈ regionPCs pc code, Quiet a ∧
      a ≠ Image.PeerGet.entry+0xaf ∧ a ≠ Image.PeerGet.entry+0x4a := by
    intro a member
    exact of_decide_eq_true (List.all_eq_true.mp quiet a member)
  exact AllowedipsOuterTrace.quiet_write fetch pc code layout s P writes run rxSection
    (fun a member before after eq => quiet_edge rxSection before after (eq ▸ (static a member).1))
    (fun a member => of_decide_eq_true (List.all_eq_true.mp interior a member))
    (fun a member => (static a member).2)

theorem initialize_trace (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch) (s : MachineData) (oldHigh oldLow : Int)
    (mappedHigh : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8 = some oldHigh)
    (mappedLow : (Allowedips.zeroHigh s).loadInt (s.regs.rsp.toBitVec+24) 8 = some oldLow)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64), rdi := 32} ∧
      t.machine.data.dmem = (Allowedips.zeroHigh s).storeInt (s.regs.rsp.toBitVec+24) 8 0 ∧
      t.machine.pc = AllowedipsImage.Lookup.entry+0x39) ∧
      Local (fun a => InRange (s.regs.rsp.toBitVec+16) 8 a ∨ InRange (s.regs.rsp.toBitVec+24) 8 a) ⟨s,AllowedipsImage.Lookup.entry+0x20⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x20⟩,[⟨s,AllowedipsImage.Lookup.entry+0x20⟩]⟩ := by
  apply quiet_region fetch _ _ ((AllowedipsLoop.layout_take AllowedipsLookup.r20_layout 4).agreement agree) s (fun t => t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64), rdi := 32} ∧
      t.data.dmem = (Allowedips.zeroHigh s).storeInt (s.regs.rsp.toBitVec+24) 8 0 ∧
      t.pc = AllowedipsImage.Lookup.entry+0x39) _ ?_ rxSection (by decide) (by decide)
  exact all_mono _ _ _ (fun t h => ⟨h,by rw [h.2.1]; exact (storeInt_frame s.dmem _ 8 0).trans (storeInt_frame (Allowedips.zeroHigh s) _ 8 0)⟩)
    (Allowedips.initializeQuery s oldHigh oldLow mappedHigh mappedLow)

#print axioms initialize_trace

theorem arguments128_trace (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch) (s : MachineData)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 0xffffff80} ∧
      t.machine.data.dmem = s.dmem ∧ t.machine.pc = AllowedipsImage.Lookup.entry+0x53) ∧
      Local (fun _ => False) ⟨s,AllowedipsImage.Lookup.entry+0x4c⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x4c⟩,[⟨s,AllowedipsImage.Lookup.entry+0x4c⟩]⟩ := by
  apply quiet_region fetch _ _ ((AllowedipsLoop.layout_take AllowedipsLookup.r4c_layout 2).agreement agree) s (fun t => t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 0xffffff80} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry+0x53) _ ?_ rxSection (by decide) (by decide)
  exact all_mono _ _ _ (fun t h => ⟨h,by rw [h.2.1]; exact by intro _ _; rfl⟩)
    (Allowedips.compare128Arguments s)

#print axioms arguments128_trace

theorem endian32_trace (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch) (s : MachineData) (network : BitVec 32) (old : Int)
    (input : s.dmem.loadInt s.regs.rbp.toBitVec 4 = some network.toNat)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 4 = some old)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = {s.regs with rax := .ofBitVec ((Allowedips.swap32 network).setWidth 64)} ∧
      t.machine.data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec+16) 4 (Allowedips.swap32 network).toInt ∧
      t.machine.pc = AllowedipsImage.Lookup.entry+0x61) ∧
      Local (InRange (s.regs.rsp.toBitVec+16) 4) ⟨s,AllowedipsImage.Lookup.entry+0x176⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x176⟩,[⟨s,AllowedipsImage.Lookup.entry+0x176⟩]⟩ := by
  apply quiet_region fetch _ _ (AllowedipsLookup.r176_layout.agreement agree) s (fun t => t.data.regs = {s.regs with rax := .ofBitVec ((Allowedips.swap32 network).setWidth 64)} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec+16) 4 (Allowedips.swap32 network).toInt ∧
      t.pc = AllowedipsImage.Lookup.entry+0x61) _ ?_ rxSection (by decide) (by decide)
  exact all_mono _ _ _ (fun t h => ⟨h,by rw [h.2.1]; exact storeInt_frame _ _ _ _⟩)
    (Allowedips.endian32 s network old input mapped)

#print axioms endian32_trace

theorem endian128_trace (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch) (s : MachineData) (high low : BitVec 64) (oldHigh oldLow : Int)
    (inputHigh : s.dmem.loadInt s.regs.rbp.toBitVec 8 = some high.toNat)
    (mappedHigh : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8 = some oldHigh)
    (inputLow : (Allowedips.highStored s high).loadInt (s.regs.rbp.toBitVec+8) 8 = some low.toNat)
    (mappedLow : (Allowedips.highStored s high).loadInt (s.regs.rsp.toBitVec+24) 8 = some oldLow)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = {s.regs with rax := .ofBitVec (Allowedips.swap64 low)} ∧
      t.machine.data.dmem = (Allowedips.highStored s high).storeInt (s.regs.rsp.toBitVec+24) 8 (Allowedips.swap64 low).toInt ∧
      t.machine.pc = AllowedipsImage.Lookup.entry+0x61) ∧
      Local (fun a => InRange (s.regs.rsp.toBitVec+16) 8 a ∨ InRange (s.regs.rsp.toBitVec+24) 8 a) ⟨s,AllowedipsImage.Lookup.entry+0x154⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x154⟩,[⟨s,AllowedipsImage.Lookup.entry+0x154⟩]⟩ := by
  apply quiet_region fetch _ _ (AllowedipsLookup.r154_layout.agreement agree) s (fun t => t.data.regs = {s.regs with rax := .ofBitVec (Allowedips.swap64 low)} ∧
      t.data.dmem = (Allowedips.highStored s high).storeInt (s.regs.rsp.toBitVec+24) 8 (Allowedips.swap64 low).toInt ∧
      t.pc = AllowedipsImage.Lookup.entry+0x61) _ ?_ rxSection (by decide) (by decide)
  exact all_mono _ _ _ (fun t h => ⟨h,by rw [h.2.1]; exact (storeInt_frame s.dmem _ 8 _).trans (storeInt_frame (Allowedips.highStored s high) _ 8 _)⟩)
    (Allowedips.endian128 s high low oldHigh oldLow inputHigh mappedHigh inputLow mappedLow)

#print axioms endian128_trace

theorem disable_trace (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch) (s : MachineData) (old : BitVec 32)
    (field : s.dmem.loadInt TrustBase.preemptCountAddress 4 = some old.toNat)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = {s.regs with r13 := .ofBitVec ((s.regs.get (.low .r12 .W8)).setWidth 64)} ∧
      t.machine.data.dmem = s.dmem.storeInt TrustBase.preemptCountAddress 4 (old+512).toInt ∧
      t.machine.pc = AllowedipsImage.Lookup.entry+0x74) ∧
      Local (InRange preemptCountAddress 4) ⟨s,AllowedipsImage.Lookup.entry+0x66⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x66⟩,[⟨s,AllowedipsImage.Lookup.entry+0x66⟩]⟩ := by
  apply quiet_region fetch _ _ (AllowedipsLookup.r66_layout.agreement agree) s (fun t => t.data.regs = {s.regs with r13 := .ofBitVec ((s.regs.get (.low .r12 .W8)).setWidth 64)} ∧
      t.data.dmem = s.dmem.storeInt TrustBase.preemptCountAddress 4 (old+512).toInt ∧
      t.pc = AllowedipsImage.Lookup.entry+0x74) _ ?_ rxSection (by decide) (by decide)
  exact all_mono _ _ _ (fun t h => ⟨h,by rw [h.2.1]; exact storeInt_frame _ _ _ _⟩)
    (Allowedips.disableBottomHalves s old field)

#print axioms disable_trace

end Binary.AllowedipsEntry
