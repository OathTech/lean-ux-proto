import AllowedipsOuterTrace
import AllowedipsOuter

namespace Binary.Allowedips
local instance : Labels := Image.linkedLabels

theorem epiloguePrefix (s : MachineData) (result bx bp r12 r13 r14 r15 : UInt64)
    (value : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some result.toNat)
    (h0 : s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+40) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+48) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+56) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+64) 8 = some r14.toNat)
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+72) 8 = some r15.toNat)
 :
    (run (AllowedipsImage.Lookup.r13c.take 8) 0x13c s).All (fun t =>
      t.data.regs = {s.regs with
        rax := result, rbx := bx, rbp := bp, r12, r13, r14, r15, rsp := s.regs.rsp+80} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry+0x14e) := by
  have add32 (x : BitVec 64) : 32+x=x+32 := BitVec.add_comm _ _
  have add32u (x : UInt64) : 32+x=x+32 := UInt64.add_comm _ _
  simp [run, AllowedipsImage.Lookup.r13c, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg, AddrExpr.interp,
    ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt,
     Effects.All, AllowedipsImage.Lookup.entry,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
      add32u, value,     ]
  simp_all [Effects.All,  ]
  decide



def returnedData (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rsp := s.regs.rsp+8}}

theorem ret_instruction (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch) (s : MachineData) (ra : UInt64)
    (loaded : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some ra.toNat) :
    instructionStep fetch ⟨s,AllowedipsImage.Lookup.entry+0x14e⟩
      (fun t => t = ⟨returnedData s,.ofBitVec ra.toBitVec⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x14e) = some _ from rfl)
  simp only [instructionStep,here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp,Operation.interp,MachineData.load,Reg64s.get64,
    Effects.All,
    Reg64s.set64,loaded,returnedData]

theorem ret_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch) (s : MachineData) (ra : UInt64)
    (loaded : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some ra.toNat) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      t.machine = ⟨returnedData s,.ofBitVec ra.toBitVec⟩ ∧
      CommonBits.Local (fun _ => False) ⟨s,AllowedipsImage.Lookup.entry+0x14e⟩ rxSection
        [(.returned "lookup",none)] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x14e⟩,[⟨s,AllowedipsImage.Lookup.entry+0x14e⟩]⟩ := by
  have executed := historySteps_eventually fetch 1 _ _ (instruction_history fetch _
    [⟨s,AllowedipsImage.Lookup.entry+0x14e⟩] _ (ret_instruction fetch agree s ra loaded))
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨machine,recorded⟩
  refine ⟨machine, ?_⟩
  refine ⟨by rw [recorded]; rfl,by rw [recorded]; rfl,?_,?_,?_,?_⟩
  · refine ⟨[LookupObservation.returned "lookup" t.machine],?_,rfl⟩
    rw [recorded]
    simp only [List.singleton_append]
    unfold observeHistory
    have edge : AllowedipsObservation.edge rxSection ⟨s,AllowedipsImage.Lookup.entry+0x14e⟩ t.machine =
        .ok [LookupObservation.returned "lookup" t.machine] := by
      simp [AllowedipsObservation.edge,AllowedipsImage.Lookup.entry,AllowedipsImage.CommonBits.entry]
      rfl
    rw [edge]
    rfl
  · rw [machine]; intro _ _; rfl
  · intro q member cut
    rw [recorded] at member
    simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · intro _ _; rfl
    · rw [machine]; intro _ _; rfl
  · intro q member
    rw [recorded] at member
    simp only [List.singleton_append,List.dropLast_cons_cons,List.dropLast_singleton,
      List.mem_singleton] at member
    rw [member]
    change AllowedipsImage.Lookup.entry+0x14e ≠ Image.PeerGet.entry+0xaf ∧
      AllowedipsImage.Lookup.entry+0x14e ≠ Image.PeerGet.entry+0x4a
    decide


theorem epilogue_prefix_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (result bx bp r12 r13 r14 r15 : UInt64)
    (value : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some result.toNat)
    (h0 : s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+40) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+48) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+56) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+64) 8 = some r14.toNat)
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+72) 8 = some r15.toNat)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = {s.regs with
        rax := result,rbx := bx,rbp := bp,r12,r13,r14,r15,rsp := s.regs.rsp+80} ∧ t.machine.data.dmem = s.dmem ∧
        t.machine.pc = AllowedipsImage.Lookup.entry+0x14e) ∧
      CommonBits.Local (fun _ => False) ⟨s,AllowedipsImage.Lookup.entry+0x13c⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x13c⟩,[⟨s,AllowedipsImage.Lookup.entry+0x13c⟩]⟩ := by
  have layout := (AllowedipsLoop.layout_take AllowedipsLookup.r13c_layout 8).agreement agree
  have static : ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.Lookup.entry+0x13c)
      (AllowedipsImage.Lookup.r13c.take 8), AllowedipsLoop.Quiet address ∧
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a := by
    intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0x13c,AllowedipsImage.Lookup.entry+0x140,
      AllowedipsImage.Lookup.entry+0x144,AllowedipsImage.Lookup.entry+0x145,AllowedipsImage.Lookup.entry+0x146,
      AllowedipsImage.Lookup.entry+0x148,AllowedipsImage.Lookup.entry+0x14a,AllowedipsImage.Lookup.entry+0x14c] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold AllowedipsLoop.Quiet <;> decide
  apply CommonBits.quiet fetch _ _ layout s (fun t =>
      t.data.regs = {s.regs with
        rax := result,rbx := bx,rbp := bp,r12,r13,r14,r15,rsp := s.regs.rsp+80} ∧ t.data.dmem = s.dmem ∧
      t.pc = AllowedipsImage.Lookup.entry+0x14e) (fun _ => False) ?_ rxSection
    (fun address member before after eq => AllowedipsLoop.quiet_edge rxSection before after (eq ▸ (static address member).1))
    ?_ (fun address member => (static address member).2)
  · exact all_mono _ _ _ (fun t h => ⟨h,h.2.1⟩) (epiloguePrefix s result bx bp r12 r13 r14 r15 value h0 h1 h2 h3 h4 h5)
  · intro address member
    change address ∈ [AllowedipsImage.Lookup.entry+0x140,AllowedipsImage.Lookup.entry+0x144,
      AllowedipsImage.Lookup.entry+0x145,AllowedipsImage.Lookup.entry+0x146,AllowedipsImage.Lookup.entry+0x148,
      AllowedipsImage.Lookup.entry+0x14a,AllowedipsImage.Lookup.entry+0x14c] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

#print axioms epilogue_prefix_trace

#print axioms ret_instruction
#print axioms ret_trace

#print axioms epiloguePrefix
end Binary.Allowedips
