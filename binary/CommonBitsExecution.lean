import CommonBitsRegions
import CommonBitsLayout
import History

namespace Binary.CommonBits
local instance : Labels := Image.linkedLabels

-- Each theorem below executes the actual decoder, with universal undefined choices.
-- These are region conclusions; they do not assert a whole helper correspondence.

theorem family32_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbx .W8) == 32 then
        AllowedipsImage.CommonBits.entry + 0x4c else AllowedipsImage.CommonBits.entry + 0x26)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x21⟩ := by
  exact region_eventually (r21_layout.agreement agree) s _
    (family32 s)

theorem family128_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbx .W8) == 128 then
        AllowedipsImage.CommonBits.entry + 0x75 else AllowedipsImage.CommonBits.entry + 0x3e)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x39⟩ := by
  exact region_eventually (r39_layout.agreement agree) s _
    (family128 s)

theorem high_equal_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbx .W64) == s.regs.get (.low .rbp .W64) then
        AllowedipsImage.CommonBits.entry + 0xc4 else AllowedipsImage.CommonBits.entry + 0x93)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x8e⟩ := by
  exact region_eventually (r8e_layout.agreement agree) s _
    (high_equal s)

theorem high_scan_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) :
    Eventually (instructionStep fetch) (fun t =>
      let x := s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec
      t.data.regs = {s.regs with
        rax := .ofBitVec x, rbx := .ofBitVec (((scan64 x).setWidth 32 + 65).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry + 0xaa)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x98⟩ := by
  exact region_eventually (r98_layout.agreement agree) s _
    (high_scan s)

theorem low_scan_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stored query : BitVec 64)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 40) 8 = some stored.toNat)
    (queryField : s.dmem.loadInt (s.regs.r13.toBitVec + 8) 8 = some query.toNat) :
    Eventually (instructionStep fetch) (fun t =>
      let x := stored ^^^ query
      t.data.regs = {s.regs with
        rax := .ofBitVec x, rbx := .ofBitVec (((scan64 x).setWidth 32 + 1).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry + 0xaa)
      ⟨s, AllowedipsImage.CommonBits.entry + 0xc9⟩ := by
  exact region_eventually (rc9_layout.agreement agree) s _
    (low_scan s stored query storedField queryField)

theorem family32_arguments_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 32, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x21 ∧ t.pc = .ofNat 0xffffffff810f40c0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x15⟩ := by
  exact region_eventually (r15_layout.agreement agree) s _
    (family32_arguments s stackWord stack)

theorem family128_arguments_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 0xffffff80, rbp := 0, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x39 ∧ t.pc = .ofNat 0xffffffff810f40c0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x2b⟩ := by
  exact region_eventually (r2b_layout.agreement agree) s _
    (family128_arguments s stackWord stack)

theorem ipv6_result_seed_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with rbp := 0xffffff80, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0xb9 ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0xaf⟩ := by
  exact region_eventually (raf_layout.agreement agree) s _
    (ipv6_result_seed s stackWord stack)

theorem high_arguments_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stored query : UInt64) (stackWord : Int)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 32) 8 = some stored.toNat)
    (queryField : s.dmem.loadInt s.regs.r13.toBitVec 8 = some query.toNat)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with
        rbx := stored, rbp := query, rdi := stored, rsi := query, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x8e ∧ t.pc = .ofNat 0xffffffff810f40a0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x7a⟩ := by
  exact region_eventually (r7a_layout.agreement agree) s _
    (high_arguments s stored query stackWord storedField queryField stack)

theorem ipv4_scan_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stored query : UInt32) (stackWord : Int)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 32) 4 = some stored.toNat)
    (queryField : s.dmem.loadInt s.regs.r13.toBitVec 4 = some query.toNat)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      let x := stored.toBitVec ^^^ query.toBitVec
      let n := scan32 x + 1
      t.data.regs = {s.regs with
        rdx := .ofBitVec (x.setWidth 64), rax := .ofBitVec (n.setWidth 64),
        rbp := .ofBitVec (((s.regs.get (.low .rbp .W32)) - n).setWidth 64),
        rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x6c ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x51⟩ := by
  exact region_eventually (r51_layout.agreement agree) s _
    (ipv4_scan s stored query stackWord storedField queryField stack)

theorem ipv6_epilogue_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (bx bp r12 r13 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec + 32) 8 = some ra.toNat) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with
        rax := .ofBitVec (((s.regs.get (.low .rbp .W32)) -
          (s.regs.get (.low .rbx .W32))).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 40} ∧
      t.data.dmem = s.dmem ∧ t.pc = .ofBitVec ra.toBitVec)
      ⟨s, AllowedipsImage.CommonBits.entry + 0xb9⟩ := by
  exact region_eventually (rb9_layout.agreement agree) s _
    (ipv6_epilogue s bx bp r12 r13 ra h0 h1 h2 h3 h4)

theorem prologue_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (stack : ∀ n < 5,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n + 1) * 8)) 8).isSome = true) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with
        r13 := s.regs.rsi, r12 := s.regs.rdi,
        rbp := .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64),
        rbx := .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64),
        rsp := s.regs.rsp - 40} ∧
      t.data.dmem = saveMemory s 5 ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x00⟩ := by
  exact region_eventually (r00_layout.agreement agree) s _
    (prologue s stack)

theorem trace_26_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (0x26 + 5) ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x26⟩ := by
  apply region_eventually (r26_layout.agreement agree) s _
  simpa [run, AllowedipsImage.CommonBits.entry, AllowedipsImage.CommonBits.r26, AllowedipsImage.CommonBits.r26] using
    (trace_call 0x26 s stackWord stack)

theorem trace_3e_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (0x3e + 5) ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x3e⟩ := by
  apply region_eventually (r3e_layout.agreement agree) s _
  simpa [run, AllowedipsImage.CommonBits.entry, AllowedipsImage.CommonBits.r3e, AllowedipsImage.CommonBits.r26] using
    (trace_call 0x3e s stackWord stack)

theorem trace_4c_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (0x4c + 5) ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x4c⟩ := by
  apply region_eventually (r4c_layout.agreement agree) s _
  simpa [run, AllowedipsImage.CommonBits.entry, AllowedipsImage.CommonBits.r4c, AllowedipsImage.CommonBits.r26] using
    (trace_call 0x4c s stackWord stack)

theorem trace_75_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (0x75 + 5) ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x75⟩ := by
  apply region_eventually (r75_layout.agreement agree) s _
  simpa [run, AllowedipsImage.CommonBits.entry, AllowedipsImage.CommonBits.r75, AllowedipsImage.CommonBits.r26] using
    (trace_call 0x75 s stackWord stack)

theorem trace_93_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (0x93 + 5) ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x93⟩ := by
  apply region_eventually (r93_layout.agreement agree) s _
  simpa [run, AllowedipsImage.CommonBits.entry, AllowedipsImage.CommonBits.r93, AllowedipsImage.CommonBits.r26] using
    (trace_call 0x93 s stackWord stack)

theorem trace_aa_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (0xaa + 5) ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0xaa⟩ := by
  apply region_eventually (raa_layout.agreement agree) s _
  simpa [run, AllowedipsImage.CommonBits.entry, AllowedipsImage.CommonBits.raa, AllowedipsImage.CommonBits.r26] using
    (trace_call 0xaa s stackWord stack)

theorem trace_c4_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (0xc4 + 5) ∧ t.pc = .ofNat 0xffffffff810f31f0)
      ⟨s, AllowedipsImage.CommonBits.entry + 0xc4⟩ := by
  apply region_eventually (rc4_layout.agreement agree) s _
  simpa [run, AllowedipsImage.CommonBits.entry, AllowedipsImage.CommonBits.rc4, AllowedipsImage.CommonBits.r26] using
    (trace_call 0xc4 s stackWord stack)

theorem return_43_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (bx bp r12 r13 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec + 32) 8 = some ra.toNat) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with
        rax := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 40} ∧
      t.data.dmem = s.dmem ∧ t.pc = .ofBitVec ra.toBitVec)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x43⟩ := by
  apply region_eventually (r43_layout.agreement agree) s _
  simpa [run, AllowedipsImage.CommonBits.entry, AllowedipsImage.CommonBits.r43, AllowedipsImage.CommonBits.r43] using
    (epilogue 0x43 s bx bp r12 r13 ra h0 h1 h2 h3 h4)

theorem return_6c_execution (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData) (bx bp r12 r13 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec + 32) 8 = some ra.toNat) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {s.regs with
        rax := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 40} ∧
      t.data.dmem = s.dmem ∧ t.pc = .ofBitVec ra.toBitVec)
      ⟨s, AllowedipsImage.CommonBits.entry + 0x6c⟩ := by
  apply region_eventually (r6c_layout.agreement agree) s _
  simpa [run, AllowedipsImage.CommonBits.entry, AllowedipsImage.CommonBits.r6c, AllowedipsImage.CommonBits.r43] using
    (epilogue 0x6c s bx bp r12 r13 ra h0 h1 h2 h3 h4)

end Binary.CommonBits
