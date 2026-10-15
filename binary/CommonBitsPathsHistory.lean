import CommonBitsFinishTrace

namespace Binary.CommonBits
open TrustBase
local instance : Labels := Image.linkedLabels

private theorem low32 (v : BitVec 32) : (v.setWidth 64).extractLsb' 0 32 = v := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

private theorem low_byte (v : BitVec 64) :
    (v.extractLsb' 0 32).setWidth 8 = v.extractLsb' 0 8 := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem low8 (v : BitVec 32) : (v.setWidth 64).extractLsb' 0 8 = v.setWidth 8 := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  rw [← BitVec.setWidth_eq_extractLsb' (by decide)]

theorem finish128_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s ((0xffffff80#32 - s.regs.get (.low .rbx .W32)).setWidth 8).toNat t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0xaa⟩ rxSection [returnedView] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0xaa⟩,[⟨s,AllowedipsImage.CommonBits.entry+0xaa⟩]⟩ := by
  apply finish_chain fetch i c s _ _ _ _ _ rxSection [] [returnedView]
    (trace_step_history fetch agree contracts 0xaa (by decide) i c apart s state rxSection)
  intro t ht bx bp
  apply finish_chain fetch i c t _ _ _ _ _ rxSection [] [returnedView]
    (seed128_step_history fetch agree contracts i c apart t ht rxSection)
  intro u hu ubx ubp
  have answer : ((u.regs.get (.low .rbp .W32)-u.regs.get (.low .rbx .W32)).setWidth 8).toNat =
      ((0xffffff80#32-s.regs.get (.low .rbx .W32)).setWidth 8).toNat := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
    rw [ubp, ubx, bx]
    rfl
  simpa only [answer] using ipv6_return_history fetch agree i c u hu rxSection returnTarget

theorem path32_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea) (family : i.family = 32)
    (bpByte : s.regs.get (.low .rbp .W8) = 32) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s i.result t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x4c⟩ rxSection [returnedView] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x4c⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x4c⟩]⟩ := by
  apply finish_chain fetch i c s _ _ _ _ _ rxSection [] [returnedView]
    (trace_step_history fetch agree contracts 0x4c (by decide) i c apart s state rxSection)
  intro t ht bx bp
  apply finish_chain fetch i c t _ _ _ _ _ rxSection [] [returnedView] (ipv4_step_history fetch agree contracts i c apart t ht rxSection family)
  intro u hu ubx ubp
  change (s.regs.get (.low .rbp .W8) : BitVec 8) = 32#8 at bpByte
  have familyWord : (t.regs.get (.low .rbp .W32)).setWidth 8 = 32#8 := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop,
      Width.bits, Nat.sub_zero, bp, low_byte] using bpByte
  have answer : (u.regs.get (.low .rbp .W8)).toNat = i.result := by
    simpa [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop,
      ubp, low8, Input.result, family] using
      ipv4_result_of_byte (t.regs.get (.low .rbp .W32)) familyWord
        (i.stored32.toBitVec ^^^ i.query32.toBitVec)
  simpa [answer, AllowedipsImage.CommonBits.entry] using simple_return_history fetch agree 0x6c (by decide) i c u hu rxSection returnTarget

theorem pathInvalid_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea)
    (not32 : i.family ≠ 32) (not128 : i.family ≠ 128) (bp : s.regs.rbp = 0) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s i.result t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x3e⟩ rxSection [returnedView] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x3e⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x3e⟩]⟩ := by
  apply finish_chain fetch i c s _ _ _ _ _ rxSection [] [returnedView]
    (trace_step_history fetch agree contracts 0x3e (by decide) i c apart s state rxSection)
  intro t ht bx tbp
  have answer : (t.regs.get (.low .rbp .W8)).toNat = i.result := by
    change i.family ≠ 32#8 at not32
    change i.family ≠ 128#8 at not128
    simp only [Input.result, if_neg not32, if_neg not128]
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop, tbp, bp, not32, not128]
  simpa [answer, AllowedipsImage.CommonBits.entry] using simple_return_history fetch agree 0x43 (by decide) i c t ht rxSection returnTarget

theorem pathHigh_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea) (family : i.family = 128)
    (different : i.storedHigh ≠ i.queryHigh)
    (stored : s.regs.rbx = i.storedHigh) (query : s.regs.rbp = i.queryHigh) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s i.result t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x93⟩ rxSection [returnedView] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x93⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x93⟩]⟩ := by
  apply finish_chain fetch i c s _ _ _ _ _ rxSection [] [returnedView]
    (trace_step_history fetch agree contracts 0x93 (by decide) i c apart s state rxSection)
  intro t ht bx bp
  apply finish_chain fetch i c t _ _ _ _ _ rxSection [] [returnedView] (high_scan_step_history fetch agree i c t ht rxSection)
  intro u hu ubx ubp
  have answer : ((0xffffff80#32-u.regs.get (.low .rbx .W32)).setWidth 8).toNat = i.result := by
    have not32 : i.family ≠ 32 := by rw [family]; decide
    rw [Input.result, if_neg not32, if_pos family, if_neg different]
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
    rw [ubx, bx, bp, stored, query]
    simp only [UInt64.toBitVec_ofBitVec, Width.bits, Nat.sub_zero, BitVec.extractLsb'_eq_self, low32, BitVec.toNat_xor]
    simpa only [BitVec.toNat_xor, UInt64.toNat_toBitVec] using ipv6_high_result (i.storedHigh.toBitVec ^^^ i.queryHigh.toBitVec)
  simpa only [answer] using finish128_history fetch agree contracts i c apart u hu rxSection returnTarget

theorem pathLow_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea) (family : i.family = 128)
    (equal : i.storedHigh = i.queryHigh) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s i.result t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0xc4⟩ rxSection [returnedView] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0xc4⟩,[⟨s,AllowedipsImage.CommonBits.entry+0xc4⟩]⟩ := by
  apply finish_chain fetch i c s _ _ _ _ _ rxSection [] [returnedView]
    (trace_step_history fetch agree contracts 0xc4 (by decide) i c apart s state rxSection)
  intro t ht bx bp
  apply finish_chain fetch i c t _ _ _ _ _ rxSection [] [returnedView] (low_scan_step_history fetch agree i c t ht rxSection family equal)
  intro u hu ubx ubp
  have answer : ((0xffffff80#32-u.regs.get (.low .rbx .W32)).setWidth 8).toNat = i.result := by
    have not32 : i.family ≠ 32 := by rw [family]; decide
    rw [Input.result, if_neg not32, if_pos family, if_pos equal]
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
    rw [ubx]
    simp only [UInt64.toBitVec_ofBitVec, Width.bits, Nat.sub_zero, BitVec.extractLsb'_eq_self, low32, BitVec.toNat_xor]
    simpa only [BitVec.toNat_xor, UInt64.toNat_toBitVec] using ipv6_low_result (i.storedLow.toBitVec ^^^ i.queryLow.toBitVec)
  simpa only [answer] using finish128_history fetch agree contracts i c apart u hu rxSection returnTarget


def Input.signature128 (i : Input) (rxSection : Nat) : List EventView :=
  [decisionView rxSection .fls128High (i.storedHigh != i.queryHigh),returnedView]

def Input.signatureOther (i : Input) (rxSection : Nat) : List EventView :=
  [decisionView rxSection .commonBits128 (i.family == 128)] ++
    if i.family = 128 then i.signature128 rxSection else [returnedView]

def Input.signature (i : Input) (rxSection : Nat) : List EventView :=
  [decisionView rxSection .commonBits32 (i.family == 32)] ++
    if i.family = 32 then [returnedView] else i.signatureOther rxSection

theorem path128_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea)
    (family : i.family = 128) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s i.result t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x75⟩ rxSection (i.signature128 rxSection) t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x75⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x75⟩]⟩ := by
  apply finish_chain fetch i c s _ _ _ _ _ rxSection [] (i.signature128 rxSection)
    (trace_step_history fetch agree contracts 0x75 (by decide) i c apart s state rxSection)
  intro t ht bx bp
  apply finish_chain fetch i c t _ _ _ _ _ rxSection [] (i.signature128 rxSection)
    (high_args_step_history fetch agree contracts i c apart t ht rxSection family)
  intro u hu ubx ubp
  apply finish_chain fetch i c u _ _ _ _ _ rxSection
    [decisionView rxSection .fls128High (i.storedHigh != i.queryHigh)] [returnedView]
    (guardHigh_step_history fetch agree i c u hu rxSection ubx ubp)
  intro v hv vbx vbp
  by_cases equal : i.storedHigh = i.queryHigh
  · simpa only [if_pos equal] using pathLow_history fetch agree contracts i c apart v hv rxSection returnTarget family equal
  · simpa only [if_neg equal] using pathHigh_history fetch agree contracts i c apart v hv rxSection returnTarget family equal
      (vbx.trans ubx) (vbp.trans ubp)

theorem pathOther_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea)
    (not32 : i.family ≠ 32) (bxByte : s.regs.get (.low .rbx .W8) = i.family) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s i.result t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x26⟩ rxSection (i.signatureOther rxSection) t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x26⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x26⟩]⟩ := by
  apply finish_chain fetch i c s _ _ _ _ _ rxSection [] (i.signatureOther rxSection)
    (trace_step_history fetch agree contracts 0x26 (by decide) i c apart s state rxSection)
  intro t ht bx bp
  apply finish_chain fetch i c t _ _ _ _ _ rxSection [] (i.signatureOther rxSection)
    (args128_step_history fetch agree contracts i c apart t ht rxSection)
  intro u hu ubx ubp
  have byte : u.regs.get (.low .rbx .W8) = i.family := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, ubx, bx] using bxByte
  apply finish_chain fetch i c u _ _ _ _ _ rxSection
    [decisionView rxSection .commonBits128 (i.family == 128)]
    (if i.family = 128 then i.signature128 rxSection else [returnedView])
    (guard128_step_history fetch agree i c u hu rxSection byte)
  intro v hv vbx vbp
  by_cases family : i.family = 128
  · simpa only [if_pos family] using path128_history fetch agree contracts i c apart v hv rxSection returnTarget family
  · simpa only [if_neg family] using pathInvalid_history fetch agree contracts i c apart v hv rxSection returnTarget not32 family
      (vbp.trans ubp)

/-- The complete common_bits body executes all paths with its actual observed
    decision sequence, exact cut frames, and all ordinary source PCs. -/
theorem body_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea)
    (bxByte : s.regs.get (.low .rbx .W8) = i.family)
    (bpByte : s.regs.get (.low .rbp .W8) = i.family) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s i.result t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0x15⟩ rxSection (i.signature rxSection) t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x15⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x15⟩]⟩ := by
  apply finish_chain fetch i c s _ _ _ _ _ rxSection [] (i.signature rxSection)
    (args32_step_history fetch agree contracts i c apart s state rxSection)
  intro t ht bx bp
  have byte : t.regs.get (.low .rbx .W8) = i.family := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, bx] using bxByte
  apply finish_chain fetch i c t _ _ _ _ _ rxSection
    [decisionView rxSection .commonBits32 (i.family == 32)]
    (if i.family = 32 then [returnedView] else i.signatureOther rxSection)
    (guard32_step_history fetch agree i c t ht rxSection byte)
  intro u hu ubx ubp
  by_cases family : i.family = 32
  · have bpByte' : u.regs.get (.low .rbp .W8) = 32 := by
      simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, ubp, bp, family] using bpByte
    simpa only [if_pos family] using path32_history fetch agree contracts i c apart u hu rxSection returnTarget family bpByte'
  · have bxByte' : u.regs.get (.low .rbx .W8) = i.family := by
      simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, ubx, bx] using bxByte
    simpa only [if_neg family] using pathOther_history fetch agree contracts i c apart u hu rxSection returnTarget family bxByte'

end Binary.CommonBits
