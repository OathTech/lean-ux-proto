import AllowedipsLoopFrame
import AllowedipsLoopObservation
import AllowedipsLayoutProofs
import AllowedipsMoves
import AllowedipsChild

namespace Binary.AllowedipsLoop
open TrustBase
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

theorem common_arguments (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xda⟩) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc = AllowedipsImage.Lookup.entry+0xe5 ∧
       t.machine.data.regs = {s.regs with
         rdi := s.regs.rbx,
         rdx := .ofBitVec ((s.regs.get (.low .r13 .W32)).setWidth 64),rsi := s.regs.rsp+16}) ∧
      Trace base coverage rxSection history events t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xda⟩,history⟩ := by
  refine scalar_trace (fetch := fetch) ((layout_take AllowedipsLookup.rda_layout 3).agreement agree)
    base s coverage (fun t => t.pc = AllowedipsImage.Lookup.entry+0xe5 ∧
      t.data.regs = {s.regs with
        rdi := s.regs.rbx, rdx := .ofBitVec ((s.regs.get (.low .r13 .W32)).setWidth 64),
        rsi := s.regs.rsp+16}) ?_ frame rxSection history events observed last ?_ ?_
  · exact all_mono _ _ _ (fun t h => ⟨⟨h.2.2,h.1⟩,h.2.1,
      by rw [h.1],by rw [h.1],by rw [h.1]⟩) (Allowedips.commonArguments s)
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0xda,AllowedipsImage.Lookup.entry+0xdd,
      AllowedipsImage.Lookup.entry+0xe0] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> unfold Quiet <;> decide
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0xdd,AllowedipsImage.Lookup.entry+0xe0] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide

theorem prefix_arguments (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (cidr : BitVec 8)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec+24) 1 = some cidr.toNat)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xea⟩) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc = AllowedipsImage.Lookup.entry+0xf7 ∧ t.machine.data.regs = {s.regs with
          r15 := .ofBitVec (cidr.setWidth 64),
          r14 := .ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64),
          rsi := .ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64),
          rdi := .ofBitVec (cidr.setWidth 64)}) ∧
      Trace base coverage rxSection history events t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xea⟩,history⟩ := by
  refine scalar_trace (fetch := fetch) ((layout_take AllowedipsLookup.rea_layout 4).agreement agree)
    base s coverage (fun t => t.pc = AllowedipsImage.Lookup.entry+0xf7 ∧
      t.data.regs = {s.regs with
          r15 := .ofBitVec (cidr.setWidth 64),
          r14 := .ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64),
          rsi := .ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64),
          rdi := .ofBitVec (cidr.setWidth 64)}) ?_ frame rxSection history events observed last ?_ ?_
  · exact all_mono _ _ _ (fun t h => ⟨⟨h.2.2,h.1⟩,h.2.1,
      by rw [h.1],by rw [h.1],by rw [h.1]⟩) (Allowedips.prefixArguments s cidr field)
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0xea,AllowedipsImage.Lookup.entry+0xef,AllowedipsImage.Lookup.entry+0xf2,AllowedipsImage.Lookup.entry+0xf4] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> unfold Quiet <;> decide
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0xef,AllowedipsImage.Lookup.entry+0xf2,AllowedipsImage.Lookup.entry+0xf4] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide

#print axioms prefix_arguments

theorem full_arguments (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xa4⟩) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc = AllowedipsImage.Lookup.entry+0xaa ∧ t.machine.data.regs = {s.regs with
          rsi := .ofBitVec ((s.regs.get (.low .r15 .W32)).setWidth 64),
          rdi := .ofBitVec ((s.regs.get (.low .r12 .W32)).setWidth 64)}) ∧
      Trace base coverage rxSection history events t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xa4⟩,history⟩ := by
  refine scalar_trace (fetch := fetch) ((layout_take AllowedipsLookup.ra4_layout 2).agreement agree)
    base s coverage (fun t => t.pc = AllowedipsImage.Lookup.entry+0xaa ∧
      t.data.regs = {s.regs with
          rsi := .ofBitVec ((s.regs.get (.low .r15 .W32)).setWidth 64),
          rdi := .ofBitVec ((s.regs.get (.low .r12 .W32)).setWidth 64)}) ?_ frame rxSection history events observed last ?_ ?_
  · exact all_mono _ _ _ (fun t h => ⟨⟨h.2.2,h.1⟩,h.2.1,
      by rw [h.1],by rw [h.1],by rw [h.1]⟩) (Allowedips.fullLengthArguments s)
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0xa4,AllowedipsImage.Lookup.entry+0xa7] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> unfold Quiet <;> decide
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0xa7] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl <;> decide

#print axioms full_arguments

theorem child_step (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (nodes peers : Nat → BitVec 64) (bits query id : Nat)
    (node : Leanux.WG.AipNode) (next : Option Nat)
    (family : bits = 32 ∨ bits = 128)
    (atNode : s.regs.rbx.toBitVec = nodes id)
    (fields : AllowedipsRelation.NodeFields s.dmem nodes peers bits query id node)
    (matching : node.cidr ≤ AllowedipsRelation.common bits node.bits query) (short : node.cidr < bits)
    (atChild : node.bit[AllowedipsRelation.childIndex node query]? = some next)
    (words : AllowedipsChild.QueryWords s.dmem (s.regs.rsp.toBitVec+16) bits query)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xb9⟩) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc = AllowedipsImage.Lookup.entry+0xd0 ∧
        t.machine.data.regs = {s.regs with
          rax := UInt64.ofNat (AllowedipsRelation.childIndex node query),
          rcx := UInt64.ofNat (7-node.cidr%8),
          rbx := UInt64.ofBitVec (AllowedipsRelation.pointer nodes next)}) ∧
      Trace base coverage rxSection history events t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xb9⟩,history⟩ := by
  refine scalar_trace (fetch := fetch) ((layout_take AllowedipsLookup.rb9_layout 6).agreement agree)
    base s coverage (fun t => t.pc = AllowedipsImage.Lookup.entry+0xd0 ∧
      t.data.regs = {s.regs with
        rax := UInt64.ofNat (AllowedipsRelation.childIndex node query),
        rcx := UInt64.ofNat (7-node.cidr%8),
        rbx := UInt64.ofBitVec (AllowedipsRelation.pointer nodes next)}) ?_
    frame rxSection history events observed last ?_ ?_
  · exact all_mono _ _ _ (fun t h => ⟨⟨h.1,h.2.2.2⟩,h.2.1,
      by rw [h.2.2.2],by rw [h.2.2.2],by rw [h.2.2.2]⟩)
      (AllowedipsChild.node_step s nodes peers bits query id node next family atNode fields matching short atChild words)
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0xb9,AllowedipsImage.Lookup.entry+0xbd,
      AllowedipsImage.Lookup.entry+0xc1,AllowedipsImage.Lookup.entry+0xc6,
      AllowedipsImage.Lookup.entry+0xc8,AllowedipsImage.Lookup.entry+0xcb] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Quiet <;> decide
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0xbd,AllowedipsImage.Lookup.entry+0xc1,
      AllowedipsImage.Lookup.entry+0xc6,AllowedipsImage.Lookup.entry+0xc8,
      AllowedipsImage.Lookup.entry+0xcb] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

#print axioms child_step

#print axioms common_arguments
end Binary.AllowedipsLoop
