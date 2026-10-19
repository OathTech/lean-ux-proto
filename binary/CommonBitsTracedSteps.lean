import CommonBitsBodyTrace

namespace Binary.CommonBits
open TrustBase
local instance : Labels := Image.linkedLabels

private def pcOffsets : List Nat := [0x26,0x3e,0x4c,0x75,0x93,0xaa,0xc4]

theorem trace_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (offset : Nat) (member : offset ∈ pcOffsets)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      BodyStep i c s (AllowedipsImage.CommonBits.entry+.ofNat (offset+5)) s.regs.rbx s.regs.rbp t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩,[⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩]⟩ := by
  have here : fetch (AllowedipsImage.CommonBits.entry+.ofNat offset) =
      some ⟨Instrumentation.callInstruction "L_ffffffff810f31f0",5⟩ := by
    apply agree
    simp only [pcOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h
    all_goals subst offset; rfl
  have silent : ∀ after, AllowedipsObservation.edge rxSection
      ⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩ after = .ok [] := by
    intro after
    simp only [pcOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h
    all_goals subst offset; rfl
  have ordinary : AllowedipsImage.CommonBits.entry+.ofNat offset ≠ Image.PeerGet.entry+0xaf ∧
      AllowedipsImage.CommonBits.entry+.ofNat offset ≠ Image.PeerGet.entry+0x4a := by
    simp only [pcOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h
    all_goals subst offset; decide
  have executed := callback_body_trace fetch _ "L_ffffffff810f31f0" here .pc contracts.pc
    i c apart s state rxSection silent ordinary
  simpa only [Int64.ofNat_add,Int64.add_assoc,show Int64.ofNat 5 = 5 from rfl] using executed

 theorem args32_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (AllowedipsImage.CommonBits.entry+0x21) s.regs.rbx s.regs.rbp t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x15⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x15⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x15⟩]⟩ := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+0x1c) =
      some ⟨Instrumentation.callInstruction "L_ffffffff810f40c0",5⟩ from rfl)
  have executed := prefix_callback_history fetch i c apart s state
    (AllowedipsImage.CommonBits.entry+0x15) (AllowedipsImage.CommonBits.entry+0x1c)
    {s.regs with rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64), rdi := 32} rxSection "L_ffffffff810f40c0" .constCmp1 contracts.constCmp1 here
    rfl rfl rfl rfl rfl (by intros; rfl) (by decide) (args32_trace fetch agree s (i.Writes c) rxSection)
  simpa only [show AllowedipsImage.CommonBits.entry+0x1c+5 = AllowedipsImage.CommonBits.entry+0x21 from rfl] using executed

 theorem args128_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (AllowedipsImage.CommonBits.entry+0x39) s.regs.rbx 0 t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x2b⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x2b⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x2b⟩]⟩ := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+0x34) =
      some ⟨Instrumentation.callInstruction "L_ffffffff810f40c0",5⟩ from rfl)
  have executed := prefix_callback_history fetch i c apart s state
    (AllowedipsImage.CommonBits.entry+0x2b) (AllowedipsImage.CommonBits.entry+0x34)
    {s.regs with rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64), rdi := 0xffffff80, rbp := 0} rxSection "L_ffffffff810f40c0" .constCmp1 contracts.constCmp1 here
    rfl rfl rfl rfl rfl (by intros; rfl) (by decide) (args128_trace fetch agree s (i.Writes c) rxSection)
  simpa only [show AllowedipsImage.CommonBits.entry+0x34+5 = AllowedipsImage.CommonBits.entry+0x39 from rfl] using executed

 theorem high_args_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) (family : i.family = 128) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (AllowedipsImage.CommonBits.entry+0x8e) i.storedHigh i.queryHigh t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x7a⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x7a⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x7a⟩]⟩ := by
  obtain ⟨stored,query⟩ := state.wordsHigh family
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+0x89) =
      some ⟨Instrumentation.callInstruction "L_ffffffff810f40a0",5⟩ from rfl)
  have executed := prefix_callback_history fetch i c apart s state
    (AllowedipsImage.CommonBits.entry+0x7a) (AllowedipsImage.CommonBits.entry+0x89)
    {s.regs with rbx := i.storedHigh, rbp := i.queryHigh, rdi := i.storedHigh, rsi := i.queryHigh} rxSection "L_ffffffff810f40a0" .cmp8 contracts.cmp8 here
    rfl rfl rfl rfl rfl (by intros; rfl) (by decide) (high_args_trace fetch agree s i.storedHigh i.queryHigh stored query (i.Writes c) rxSection)
  simpa only [show AllowedipsImage.CommonBits.entry+0x89+5 = AllowedipsImage.CommonBits.entry+0x8e from rfl] using executed

 theorem ipv4_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) (family : i.family = 32) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (AllowedipsImage.CommonBits.entry+0x6c) s.regs.rbx
        (.ofBitVec (((s.regs.get (.low .rbp .W32)) -
          (scan32 (i.stored32.toBitVec ^^^ i.query32.toBitVec)+1)).setWidth 64)) t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x51⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x51⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x51⟩]⟩ := by
  obtain ⟨stored,query⟩ := state.words32 family
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+0x67) =
      some ⟨Instrumentation.callInstruction "L_ffffffff810f31f0",5⟩ from rfl)
  have executed := prefix_callback_history fetch i c apart s state
    (AllowedipsImage.CommonBits.entry+0x51) (AllowedipsImage.CommonBits.entry+0x67)
    {s.regs with rdx := .ofBitVec ((i.stored32.toBitVec ^^^ i.query32.toBitVec).setWidth 64), rax := .ofBitVec ((scan32 (i.stored32.toBitVec ^^^ i.query32.toBitVec)+1).setWidth 64), rbp := .ofBitVec (((s.regs.get (.low .rbp .W32))-(scan32 (i.stored32.toBitVec ^^^ i.query32.toBitVec)+1)).setWidth 64)} rxSection "L_ffffffff810f31f0" .pc contracts.pc here
    rfl rfl rfl rfl rfl (by intros; rfl) (by decide) (ipv4_trace fetch agree s i.stored32 i.query32 stored query (i.Writes c) rxSection)
  simpa only [show AllowedipsImage.CommonBits.entry+0x67+5 = AllowedipsImage.CommonBits.entry+0x6c from rfl] using executed

 theorem seed128_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (AllowedipsImage.CommonBits.entry+0xb9) s.regs.rbx 0xffffff80 t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0xaf⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0xaf⟩,[⟨s,AllowedipsImage.CommonBits.entry+0xaf⟩]⟩ := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+0xb4) =
      some ⟨Instrumentation.callInstruction "L_ffffffff810f31f0",5⟩ from rfl)
  have executed := prefix_callback_history fetch i c apart s state
    (AllowedipsImage.CommonBits.entry+0xaf) (AllowedipsImage.CommonBits.entry+0xb4)
    {s.regs with rbp := 0xffffff80} rxSection "L_ffffffff810f31f0" .pc contracts.pc here
    rfl rfl rfl rfl rfl (by intros; rfl) (by decide) (seed128_trace fetch agree s (i.Writes c) rxSection)
  simpa only [show AllowedipsImage.CommonBits.entry+0xb4+5 = AllowedipsImage.CommonBits.entry+0xb9 from rfl] using executed


theorem guard32_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) (family : s.regs.get (.low .rbx .W8) = i.family) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (if i.family = 32 then AllowedipsImage.CommonBits.entry+0x4c else
        AllowedipsImage.CommonBits.entry+0x26) s.regs.rbx s.regs.rbp t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x21⟩ rxSection [decisionView rxSection .commonBits32 (i.family == 32)] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x21⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x21⟩]⟩ := by
  apply pure_body_trace fetch i c s state (AllowedipsImage.CommonBits.entry+0x21) _
    s.regs rxSection [decisionView rxSection .commonBits32 (i.family == 32)] rfl rfl rfl rfl rfl
  simpa only [family, beq_iff_eq] using family32_trace fetch agree s (i.Writes c) rxSection

theorem guard128_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) (family : s.regs.get (.low .rbx .W8) = i.family) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (if i.family = 128 then AllowedipsImage.CommonBits.entry+0x75 else
        AllowedipsImage.CommonBits.entry+0x3e) s.regs.rbx s.regs.rbp t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x39⟩ rxSection [decisionView rxSection .commonBits128 (i.family == 128)] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x39⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x39⟩]⟩ := by
  apply pure_body_trace fetch i c s state (AllowedipsImage.CommonBits.entry+0x39) _
    s.regs rxSection [decisionView rxSection .commonBits128 (i.family == 128)] rfl rfl rfl rfl rfl
  simpa only [family, beq_iff_eq] using family128_trace fetch agree s (i.Writes c) rxSection

theorem guardHigh_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (stored : s.regs.rbx = i.storedHigh) (query : s.regs.rbp = i.queryHigh) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (if i.storedHigh = i.queryHigh then AllowedipsImage.CommonBits.entry+0xc4 else
        AllowedipsImage.CommonBits.entry+0x93) s.regs.rbx s.regs.rbp t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x8e⟩ rxSection [decisionView rxSection .fls128High (i.storedHigh != i.queryHigh)] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x8e⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x8e⟩]⟩ := by
  apply pure_body_trace fetch i c s state (AllowedipsImage.CommonBits.entry+0x8e) _
    s.regs rxSection [decisionView rxSection .fls128High (i.storedHigh != i.queryHigh)] rfl rfl rfl rfl rfl
  have compare : (i.storedHigh.toBitVec == i.queryHigh.toBitVec) = (i.storedHigh == i.queryHigh) := by
    apply Bool.eq_iff_iff.mpr
    simp [UInt64.toBitVec_inj]
  simpa [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    stored, query, UInt64.toBitVec_inj, decisionView, compare, bne_eq] using high_equal_trace fetch agree s (i.Writes c) rxSection

theorem high_scan_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (AllowedipsImage.CommonBits.entry+0xaa)
        (.ofBitVec (((scan64 (s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec)).setWidth 32+65).setWidth 64))
        s.regs.rbp t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x98⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x98⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x98⟩]⟩ := by
  apply pure_body_trace fetch i c s state (AllowedipsImage.CommonBits.entry+0x98) _
    {s.regs with rax := .ofBitVec (s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec), rbx := .ofBitVec (((scan64 (s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec)).setWidth 32+65).setWidth 64)} rxSection [] rfl rfl rfl rfl rfl
  exact high_scan_trace fetch agree s (i.Writes c) rxSection

theorem low_scan_step_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat) (family : i.family = 128)
    (equal : i.storedHigh = i.queryHigh) :
    Eventually (historyStep fetch) (fun t => BodyStep i c s (AllowedipsImage.CommonBits.entry+0xaa)
        (.ofBitVec (((scan64 (i.storedLow.toBitVec ^^^ i.queryLow.toBitVec)).setWidth 32+1).setWidth 64))
        s.regs.rbp t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0xc9⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0xc9⟩,[⟨s,AllowedipsImage.CommonBits.entry+0xc9⟩]⟩ := by
  obtain ⟨stored,query⟩ := state.wordsLow family equal
  apply pure_body_trace fetch i c s state (AllowedipsImage.CommonBits.entry+0xc9) _
    {s.regs with rax := .ofBitVec (i.storedLow.toBitVec ^^^ i.queryLow.toBitVec), rbx := .ofBitVec (((scan64 (i.storedLow.toBitVec ^^^ i.queryLow.toBitVec)).setWidth 32+1).setWidth 64)} rxSection [] rfl rfl rfl rfl rfl
  exact low_scan_trace fetch agree s i.storedLow.toBitVec i.queryLow.toBitVec stored query (i.Writes c) rxSection

end Binary.CommonBits
