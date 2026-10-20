import CommonBitsFinish

namespace Binary.CommonBits.Sequential
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

theorem finish128_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) :
    Eventually (instructionStep fetch) (ReturnPost i c s ((0xffffff80#32 - s.regs.get (.low .rbx .W32)).setWidth 8).toNat)
      ⟨s,AllowedipsImage.CommonBits.entry+0xaa⟩ := by
  apply chain_step fetch i c s _ _ _ _ _
    (trace_step fetch agree contracts 0xaa raa_layout i c apart s state)
  intro t ht bx bp
  apply chain_step fetch i c t _ _ _ _ _
    (seed128_step fetch agree contracts i c apart t ht)
  intro u hu ubx ubp
  have answer : ((u.regs.get (.low .rbp .W32)-u.regs.get (.low .rbx .W32)).setWidth 8).toNat =
      ((0xffffff80#32-s.regs.get (.low .rbx .W32)).setWidth 8).toNat := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
    rw [ubp, ubx, bx]
    rfl
  simpa only [answer] using ipv6_return fetch agree i c u hu

theorem path32_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s)
    (family : i.family = 32)
    (bpByte : s.regs.get (.low .rbp .W8) = 32) :
    Eventually (instructionStep fetch) (ReturnPost i c s i.result)
      ⟨s,AllowedipsImage.CommonBits.entry+0x4c⟩ := by
  apply chain_step fetch i c s _ _ _ _ _
    (trace_step fetch agree contracts 0x4c r4c_layout i c apart s state)
  intro t ht bx bp
  apply chain_step fetch i c t _ _ _ _ _
    (ipv4_step fetch agree contracts i c apart t ht family)
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
  simpa [answer, AllowedipsImage.CommonBits.entry] using simple_return fetch agree 0x6c r6c_layout i c u hu

theorem pathInvalid_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s)
    (not32 : i.family ≠ 32) (not128 : i.family ≠ 128) (bp : s.regs.rbp = 0) :
    Eventually (instructionStep fetch) (ReturnPost i c s i.result)
      ⟨s,AllowedipsImage.CommonBits.entry+0x3e⟩ := by
  apply chain_step fetch i c s _ _ _ _ _
    (trace_step fetch agree contracts 0x3e r3e_layout i c apart s state)
  intro t ht bx tbp
  have answer : (t.regs.get (.low .rbp .W8)).toNat = i.result := by
    change i.family ≠ 32#8 at not32
    change i.family ≠ 128#8 at not128
    simp only [Input.result, ]
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop, tbp, bp, not32, not128]
  simpa [answer, AllowedipsImage.CommonBits.entry] using simple_return fetch agree 0x43 r43_layout i c t ht

theorem pathHigh_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s)
    (family : i.family = 128)
    (different : i.storedHigh ≠ i.queryHigh)
    (stored : s.regs.rbx = i.storedHigh) (query : s.regs.rbp = i.queryHigh) :
    Eventually (instructionStep fetch) (ReturnPost i c s i.result)
      ⟨s,AllowedipsImage.CommonBits.entry+0x93⟩ := by
  apply chain_step fetch i c s _ _ _ _ _
    (trace_step fetch agree contracts 0x93 r93_layout i c apart s state)
  intro t ht bx bp
  apply chain_step fetch i c t _ _ _ _ _
    (high_scan_step fetch agree i c t ht)
  intro u hu ubx ubp
  have answer : ((0xffffff80#32-u.regs.get (.low .rbx .W32)).setWidth 8).toNat = i.result := by
    have not32 : i.family ≠ 32 := by rw [family]; decide
    rw [Input.result, ite_eq_right not32, ite_eq_left family, ite_eq_right different]
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
    rw [ubx, bx, bp, stored, query]
    simp only [ Width.bits, Nat.sub_zero, BitVec.extractLsb'_eq_self, low32]
    simpa only [BitVec.toNat_xor, UInt64.toNat_toBitVec] using ipv6_high_result (i.storedHigh.toBitVec ^^^ i.queryHigh.toBitVec)
  simpa only [answer] using finish128_run fetch agree contracts i c apart u hu

theorem pathLow_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s)
    (family : i.family = 128)
    (equal : i.storedHigh = i.queryHigh) :
    Eventually (instructionStep fetch) (ReturnPost i c s i.result)
      ⟨s,AllowedipsImage.CommonBits.entry+0xc4⟩ := by
  apply chain_step fetch i c s _ _ _ _ _
    (trace_step fetch agree contracts 0xc4 rc4_layout i c apart s state)
  intro t ht bx bp
  apply chain_step fetch i c t _ _ _ _ _
    (low_scan_step fetch agree i c t ht family equal)
  intro u hu ubx ubp
  have answer : ((0xffffff80#32-u.regs.get (.low .rbx .W32)).setWidth 8).toNat = i.result := by
    have not32 : i.family ≠ 32 := by rw [family]; decide
    rw [Input.result, ite_eq_right not32, ite_eq_left family, ite_eq_left equal]
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
    rw [ubx]
    simp only [ Width.bits, Nat.sub_zero, BitVec.extractLsb'_eq_self, low32]
    simpa only [BitVec.toNat_xor, UInt64.toNat_toBitVec] using ipv6_low_result (i.storedLow.toBitVec ^^^ i.queryLow.toBitVec)
  simpa only [answer] using finish128_run fetch agree contracts i c apart u hu


theorem path128_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s)
    (family : i.family = 128) :
    Eventually (instructionStep fetch) (ReturnPost i c s i.result)
      ⟨s,AllowedipsImage.CommonBits.entry+0x75⟩ := by
  apply chain_step fetch i c s _ _ _ _ _
    (trace_step fetch agree contracts 0x75 r75_layout i c apart s state)
  intro t ht bx bp
  apply chain_step fetch i c t _ _ _ _ _
    (high_args_step fetch agree contracts i c apart t ht family)
  intro u hu ubx ubp
  apply chain_step fetch i c u _ _ _ _ _
    (guardHigh_step fetch agree i c u hu ubx ubp)
  intro v hv vbx vbp
  by_cases equal : i.storedHigh = i.queryHigh
  · simpa only [ite_eq_left equal] using pathLow_run fetch agree contracts i c apart v hv family equal
  · simpa only [ite_eq_right equal] using pathHigh_run fetch agree contracts i c apart v hv family equal
      (vbx.trans ubx) (vbp.trans ubp)

theorem pathOther_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s)
    (not32 : i.family ≠ 32) (bxByte : s.regs.get (.low .rbx .W8) = i.family) :
    Eventually (instructionStep fetch) (ReturnPost i c s i.result)
      ⟨s,AllowedipsImage.CommonBits.entry+0x26⟩ := by
  apply chain_step fetch i c s _ _ _ _ _
    (trace_step fetch agree contracts 0x26 r26_layout i c apart s state)
  intro t ht bx bp
  apply chain_step fetch i c t _ _ _ _ _
    (args128_step fetch agree contracts i c apart t ht)
  intro u hu ubx ubp
  have byte : u.regs.get (.low .rbx .W8) = i.family := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, ubx, bx] using bxByte
  apply chain_step fetch i c u _ _ _ _ _
    (guard128_step fetch agree i c u hu byte)
  intro v hv vbx vbp
  by_cases family : i.family = 128
  · simpa only [ite_eq_left family] using path128_run fetch agree contracts i c apart v hv family
  · simpa only [ite_eq_right family] using pathInvalid_run fetch agree contracts i c apart v hv not32 family
      (vbp.trans ubp)

/-- All physical body paths, with an arbitrary return word. Internal decision
    observations are not part of this reusable sequential contract. -/
theorem body_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s)
    (bxByte : s.regs.get (.low .rbx .W8) = i.family)
    (bpByte : s.regs.get (.low .rbp .W8) = i.family) :
    Eventually (instructionStep fetch) (ReturnPost i c s i.result)
      ⟨s,AllowedipsImage.CommonBits.entry+0x15⟩ := by
  apply chain_step fetch i c s _ _ _ _ _
    (args32_step fetch agree contracts i c apart s state)
  intro t ht bx bp
  have byte : t.regs.get (.low .rbx .W8) = i.family := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, bx] using bxByte
  apply chain_step fetch i c t _ _ _ _ _
    (guard32_step fetch agree i c t ht byte)
  intro u hu ubx ubp
  by_cases family : i.family = 32
  · have bpByte' : u.regs.get (.low .rbp .W8) = 32 := by
      simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, ubp, bp, family] using bpByte
    simpa only [ite_eq_left family] using path32_run fetch agree contracts i c apart u hu family bpByte'
  · have bxByte' : u.regs.get (.low .rbx .W8) = i.family := by
      simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, ubx, bx] using bxByte
    simpa only [ite_eq_right family] using pathOther_run fetch agree contracts i c apart u hu family bxByte'

#print axioms body_run
end Binary.CommonBits.Sequential
