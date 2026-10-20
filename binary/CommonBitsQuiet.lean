import CommonBitsTrace

namespace Binary.CommonBits
local instance : Labels := Image.linkedLabels

private theorem args32_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x15) (AllowedipsImage.CommonBits.r15.take 2),
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0x15, AllowedipsImage.CommonBits.entry+0x17] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h
  all_goals rw [h] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

private theorem args32_noInterior :
    ∀ address ∈ (AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x15) (AllowedipsImage.CommonBits.r15.take 2)).tail,
      ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints) := by decide
private theorem args32_ordinary :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x15) (AllowedipsImage.CommonBits.r15.take 2),
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a := by decide

/-- Actual silent prefix through its final physical state, preserving all cuts. -/
theorem args32_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (let t := t.machine; t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x1c) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x15⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x15⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x15⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0x15) (AllowedipsImage.CommonBits.r15.take 2)
    ((layout_take r15_layout 2).agreement agree)
    s (fun t => t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x1c) writes ?_ rxSection (args32_silent rxSection) args32_noInterior args32_ordinary
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩) (family32_arguments_prefix s)

private theorem args128_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x2b) (AllowedipsImage.CommonBits.r2b.take 3),
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0x2b, AllowedipsImage.CommonBits.entry+0x2d, AllowedipsImage.CommonBits.entry+0x32] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h
  all_goals rw [h] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

private theorem args128_noInterior :
    ∀ address ∈ (AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x2b) (AllowedipsImage.CommonBits.r2b.take 3)).tail,
      ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints) := by decide
private theorem args128_ordinary :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x2b) (AllowedipsImage.CommonBits.r2b.take 3),
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a := by decide

/-- Actual silent prefix through its final physical state, preserving all cuts. -/
theorem args128_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (let t := t.machine; t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 0xffffff80, rbp := 0} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x34) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x2b⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x2b⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x2b⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0x2b) (AllowedipsImage.CommonBits.r2b.take 3)
    ((layout_take r2b_layout 3).agreement agree)
    s (fun t => t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 0xffffff80, rbp := 0} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x34) writes ?_ rxSection (args128_silent rxSection) args128_noInterior args128_ordinary
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩) (family128_arguments_prefix s)

private theorem seed128_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0xaf) (AllowedipsImage.CommonBits.raf.take 1),
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0xaf] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rw [member] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

private theorem seed128_noInterior :
    ∀ address ∈ (AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0xaf) (AllowedipsImage.CommonBits.raf.take 1)).tail,
      ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints) := by decide
private theorem seed128_ordinary :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0xaf) (AllowedipsImage.CommonBits.raf.take 1),
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a := by decide

/-- Actual silent prefix through its final physical state, preserving all cuts. -/
theorem seed128_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (let t := t.machine; t.data.regs = {s.regs with rbp := 0xffffff80} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0xb4) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0xaf⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0xaf⟩,[⟨s,AllowedipsImage.CommonBits.entry+0xaf⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0xaf) (AllowedipsImage.CommonBits.raf.take 1)
    ((layout_take raf_layout 1).agreement agree)
    s (fun t => t.data.regs = {s.regs with rbp := 0xffffff80} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0xb4) writes ?_ rxSection (seed128_silent rxSection) seed128_noInterior seed128_ordinary
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩) (ipv6_result_seed_prefix s)

private theorem high_args_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x7a) (AllowedipsImage.CommonBits.r7a.take 4),
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0x7a, AllowedipsImage.CommonBits.entry+0x7f, AllowedipsImage.CommonBits.entry+0x83, AllowedipsImage.CommonBits.entry+0x86] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h
  all_goals rw [h] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

private theorem high_args_noInterior :
    ∀ address ∈ (AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x7a) (AllowedipsImage.CommonBits.r7a.take 4)).tail,
      ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints) := by decide
private theorem high_args_ordinary :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x7a) (AllowedipsImage.CommonBits.r7a.take 4),
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a := by decide

/-- Actual silent prefix through its final physical state, preserving all cuts. -/
theorem high_args_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (stored query : UInt64)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 32) 8 = some stored.toNat)
    (queryField : s.dmem.loadInt s.regs.r13.toBitVec 8 = some query.toNat) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (let t := t.machine; t.data.regs = {s.regs with
        rbx := stored, rbp := query, rdi := stored, rsi := query} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x89) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x7a⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x7a⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x7a⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0x7a) (AllowedipsImage.CommonBits.r7a.take 4)
    ((layout_take r7a_layout 4).agreement agree)
    s (fun t => t.data.regs = {s.regs with
        rbx := stored, rbp := query, rdi := stored, rsi := query} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x89) writes ?_ rxSection (high_args_silent rxSection) high_args_noInterior high_args_ordinary
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩) (high_arguments_prefix s stored query storedField queryField)

private theorem ipv4_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x51) (AllowedipsImage.CommonBits.r51.take 6),
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0x51, AllowedipsImage.CommonBits.entry+0x56, AllowedipsImage.CommonBits.entry+0x5b, AllowedipsImage.CommonBits.entry+0x5f, AllowedipsImage.CommonBits.entry+0x62, AllowedipsImage.CommonBits.entry+0x65] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h
  all_goals rw [h] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

private theorem ipv4_noInterior :
    ∀ address ∈ (AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x51) (AllowedipsImage.CommonBits.r51.take 6)).tail,
      ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints) := by decide
private theorem ipv4_ordinary :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x51) (AllowedipsImage.CommonBits.r51.take 6),
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a := by decide

/-- Actual silent prefix through its final physical state, preserving all cuts. -/
theorem ipv4_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (stored query : UInt32)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 32) 4 = some stored.toNat)
    (queryField : s.dmem.loadInt s.regs.r13.toBitVec 4 = some query.toNat) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (let t := t.machine; let x := stored.toBitVec ^^^ query.toBitVec
      let n := scan32 x + 1
      t.data.regs = {s.regs with
        rdx := .ofBitVec (x.setWidth 64), rax := .ofBitVec (n.setWidth 64),
        rbp := .ofBitVec (((s.regs.get (.low .rbp .W32)) - n).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x67) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x51⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x51⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x51⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0x51) (AllowedipsImage.CommonBits.r51.take 6)
    ((layout_take r51_layout 6).agreement agree)
    s (fun t => let x := stored.toBitVec ^^^ query.toBitVec
      let n := scan32 x + 1
      t.data.regs = {s.regs with
        rdx := .ofBitVec (x.setWidth 64), rax := .ofBitVec (n.setWidth 64),
        rbp := .ofBitVec (((s.regs.get (.low .rbp .W32)) - n).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x67) writes ?_ rxSection (ipv4_silent rxSection) ipv4_noInterior ipv4_ordinary
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩) (ipv4_scan_prefix s stored query storedField queryField)

private theorem high_scan_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x98) AllowedipsImage.CommonBits.r98,
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0x98, AllowedipsImage.CommonBits.entry+0x9b, AllowedipsImage.CommonBits.entry+0xa0, AllowedipsImage.CommonBits.entry+0xa3, AllowedipsImage.CommonBits.entry+0xa7] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h
  all_goals rw [h] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

private theorem high_scan_noInterior :
    ∀ address ∈ (AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x98) AllowedipsImage.CommonBits.r98).tail,
      ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints) := by decide
private theorem high_scan_ordinary :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x98) AllowedipsImage.CommonBits.r98,
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a := by decide

/-- Actual silent prefix through its final physical state, preserving all cuts. -/
theorem high_scan_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (let t := t.machine; let x := s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec
      t.data.regs = {s.regs with
        rax := .ofBitVec x, rbx := .ofBitVec (((scan64 x).setWidth 32 + 65).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry + 0xaa) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x98⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x98⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x98⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0x98) AllowedipsImage.CommonBits.r98
    ((r98_layout).agreement agree)
    s (fun t => let x := s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec
      t.data.regs = {s.regs with
        rax := .ofBitVec x, rbx := .ofBitVec (((scan64 x).setWidth 32 + 65).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry + 0xaa) writes ?_ rxSection (high_scan_silent rxSection) high_scan_noInterior high_scan_ordinary
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩) (high_scan s)

private theorem low_scan_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0xc9) AllowedipsImage.CommonBits.rc9,
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0xc9, AllowedipsImage.CommonBits.entry+0xce, AllowedipsImage.CommonBits.entry+0xd3, AllowedipsImage.CommonBits.entry+0xd7, AllowedipsImage.CommonBits.entry+0xdb, AllowedipsImage.CommonBits.entry+0xde] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h
  all_goals rw [h] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

private theorem low_scan_noInterior :
    ∀ address ∈ (AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0xc9) AllowedipsImage.CommonBits.rc9).tail,
      ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints) := by decide
private theorem low_scan_ordinary :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0xc9) AllowedipsImage.CommonBits.rc9,
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a := by decide

/-- Actual silent prefix through its final physical state, preserving all cuts. -/
theorem low_scan_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (stored query : BitVec 64)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 40) 8 = some stored.toNat)
    (queryField : s.dmem.loadInt (s.regs.r13.toBitVec + 8) 8 = some query.toNat) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (let t := t.machine; let x := stored ^^^ query
      t.data.regs = {s.regs with
        rax := .ofBitVec x, rbx := .ofBitVec (((scan64 x).setWidth 32 + 1).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry + 0xaa) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0xc9⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0xc9⟩,[⟨s,AllowedipsImage.CommonBits.entry+0xc9⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0xc9) AllowedipsImage.CommonBits.rc9
    ((rc9_layout).agreement agree)
    s (fun t => let x := stored ^^^ query
      t.data.regs = {s.regs with
        rax := .ofBitVec x, rbx := .ofBitVec (((scan64 x).setWidth 32 + 1).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry + 0xaa) writes ?_ rxSection (low_scan_silent rxSection) low_scan_noInterior low_scan_ordinary
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩) (low_scan s stored query storedField queryField)

end Binary.CommonBits
