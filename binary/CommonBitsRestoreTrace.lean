import CommonBitsReturnTrace

namespace Binary.CommonBits
local instance : Labels := Image.linkedLabels

private theorem return43_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x43) (AllowedipsImage.CommonBits.r43.take 5),
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0x43, AllowedipsImage.CommonBits.entry+0x45, AllowedipsImage.CommonBits.entry+0x46, AllowedipsImage.CommonBits.entry+0x47, AllowedipsImage.CommonBits.entry+0x49] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h
  all_goals rw [h] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

theorem return43_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (bx bp r12 r13 : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t => (let t := t.machine; t.data.regs = {s.regs with
        rax := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+.ofNat (0x43+8)) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x43⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x43⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x43⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0x43) (AllowedipsImage.CommonBits.r43.take 5) ((layout_take r43_layout 5).agreement agree)
    s (fun t => t.data.regs = {s.regs with
        rax := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+.ofNat (0x43+8)) writes ?_ rxSection (return43_silent rxSection) (by decide) (by decide)
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩)
    (epilogue_prefix 0x43 s bx bp r12 r13 h0 h1 h2 h3)

private theorem return6c_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0x6c) (AllowedipsImage.CommonBits.r6c.take 5),
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0x6c, AllowedipsImage.CommonBits.entry+0x6e, AllowedipsImage.CommonBits.entry+0x6f, AllowedipsImage.CommonBits.entry+0x70, AllowedipsImage.CommonBits.entry+0x72] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h
  all_goals rw [h] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

theorem return6c_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (bx bp r12 r13 : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t => (let t := t.machine; t.data.regs = {s.regs with
        rax := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+.ofNat (0x6c+8)) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x6c⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x6c⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x6c⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0x6c) (AllowedipsImage.CommonBits.r6c.take 5) ((layout_take r6c_layout 5).agreement agree)
    s (fun t => t.data.regs = {s.regs with
        rax := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+.ofNat (0x6c+8)) writes ?_ rxSection (return6c_silent rxSection) (by decide) (by decide)
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩)
    (epilogue_prefix 0x6c s bx bp r12 r13 h0 h1 h2 h3)

private theorem return128_silent (rxSection : Nat) :
    ∀ address ∈ AllowedipsLoop.regionPCs (AllowedipsImage.CommonBits.entry+0xb9) (AllowedipsImage.CommonBits.rb9.take 6),
      ∀ before after, before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [] := by
  intro address member before after here
  change address ∈ [AllowedipsImage.CommonBits.entry+0xb9, AllowedipsImage.CommonBits.entry+0xbb, AllowedipsImage.CommonBits.entry+0xbc, AllowedipsImage.CommonBits.entry+0xbe, AllowedipsImage.CommonBits.entry+0xbf, AllowedipsImage.CommonBits.entry+0xc1] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h
  all_goals rw [h] at here
  all_goals unfold AllowedipsObservation.edge; rw [here]; rfl

theorem return128_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch)
    (s : MachineData) (bx bp r12 r13 : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat) (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t => (let t := t.machine; t.data.regs = {s.regs with
        rax := .ofBitVec (((s.regs.get (.low .rbp .W32)) -
          (s.regs.get (.low .rbx .W32))).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0xc3) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0xb9⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0xb9⟩,[⟨s,AllowedipsImage.CommonBits.entry+0xb9⟩]⟩ := by
  apply quiet fetch (AllowedipsImage.CommonBits.entry+0xb9) (AllowedipsImage.CommonBits.rb9.take 6) ((layout_take rb9_layout 6).agreement agree)
    s (fun t => t.data.regs = {s.regs with
        rax := .ofBitVec (((s.regs.get (.low .rbp .W32)) -
          (s.regs.get (.low .rbx .W32))).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0xc3) writes ?_ rxSection (return128_silent rxSection) (by decide) (by decide)
  exact all_mono _ _ _ (fun _ h => ⟨h,h.2.1⟩)
    (ipv6_epilogue_prefix s bx bp r12 r13 h0 h1 h2 h3)

end Binary.CommonBits
