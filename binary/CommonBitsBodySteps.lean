import CommonBitsBodyState

namespace Binary.CommonBits
open TrustBase
local instance : Labels := Image.linkedLabels

structure Callbacks (fetch : Int64 → Option Decoded) : Prop where
  pc : AllowedipsTracePcContract fetch
  constCmp1 : AllowedipsTraceConstCmp1Contract fetch
  cmp8 : AllowedipsTraceCmp8Contract fetch

structure BodyStep (i : Input) (c : CommonBitsCoverage.Context) (before : MachineData)
    (pc : Int64) (bx bp : UInt64) (after : MachineState) : Prop where
  atPC : after.pc = pc
  body : BodyAt i c after.data
  rbx : after.data.regs.rbx = bx
  rbp : after.data.regs.rbp = bp
  r14 : after.data.regs.r14 = before.regs.r14
  r15 : after.data.regs.r15 = before.regs.r15
  frame : EqualOutside (i.Writes c) before.dmem after.data.dmem

theorem callback_step (fetch : Int64 → Option Decoded) (address returnPC : Int64)
    (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch address
      (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (initial : MachineState) (s : MachineData) (state : BodyAt i c s) (registers : Reg64s)
    (node : registers.r12 = s.regs.r12) (key : registers.r13 = s.regs.r13)
    (r14 : registers.r14 = s.regs.r14) (r15 : registers.r15 = s.regs.r15)
    (region : Eventually (instructionStep fetch) (fun t =>
      t.data.regs = {registers with rsp := s.regs.rsp-8} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt ∧
      t.pc = address) initial) :
    Eventually (instructionStep fetch) (BodyStep i c s returnPC registers.rbx registers.rbp) initial := by
  have run := CommonBitsCoverage.region_callback fetch address returnPC kind contract
    c initial s registers state.ready region
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pc, sp, bx, bp, r12, r13, a14, a15, ready, frame⟩
  exact ⟨pc, state.after_callback apart ready sp (r12.trans node) (r13.trans key) frame,
    bx, bp, a14.trans r14, a15.trans r15, by
      intro a outside
      exact frame a (by simpa [Input.Writes, state.stack] using outside)⟩

/-- Each singleton PC callback uses the same proved CALL region, at its own layout. -/
theorem trace_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (offset : Nat)
    (layout : LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+.ofNat offset)
      AllowedipsImage.CommonBits.r26)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (AllowedipsImage.CommonBits.entry+.ofNat (offset+5)) s.regs.rbx s.regs.rbp)
      ⟨s, AllowedipsImage.CommonBits.entry+.ofNat offset⟩ := by
  obtain ⟨word, mapped⟩ := Option.isSome_iff_exists.mp state.ready.mapped
  apply callback_step fetch (.ofNat 0xffffffff810f31f0) _ .pc contracts.pc i c apart _ s state s.regs
    rfl rfl rfl rfl
  exact region_eventually (layout.agreement agree) s _ (trace_call offset s word mapped)

theorem args32_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (AllowedipsImage.CommonBits.entry+0x21) s.regs.rbx s.regs.rbp)
      ⟨s, AllowedipsImage.CommonBits.entry+0x15⟩ := by
  obtain ⟨word, mapped⟩ := Option.isSome_iff_exists.mp state.ready.mapped
  apply callback_step fetch (.ofNat 0xffffffff810f40c0) _ .constCmp1 contracts.constCmp1 i c apart _ s state
    {s.regs with rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64), rdi := 32}
    rfl rfl rfl rfl
  exact family32_arguments_execution fetch agree s word mapped

theorem args128_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (AllowedipsImage.CommonBits.entry+0x39) s.regs.rbx 0)
      ⟨s, AllowedipsImage.CommonBits.entry+0x2b⟩ := by
  obtain ⟨word, mapped⟩ := Option.isSome_iff_exists.mp state.ready.mapped
  apply callback_step fetch (.ofNat 0xffffffff810f40c0) _ .constCmp1 contracts.constCmp1 i c apart _ s state
    {s.regs with rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64), rdi := 0xffffff80, rbp := 0}
    rfl rfl rfl rfl
  exact family128_arguments_execution fetch agree s word mapped

theorem high_args_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (family : i.family = 128) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (AllowedipsImage.CommonBits.entry+0x8e) i.storedHigh i.queryHigh)
      ⟨s, AllowedipsImage.CommonBits.entry+0x7a⟩ := by
  obtain ⟨word, mapped⟩ := Option.isSome_iff_exists.mp state.ready.mapped
  obtain ⟨stored, query⟩ := state.wordsHigh family
  apply callback_step fetch (.ofNat 0xffffffff810f40a0) _ .cmp8 contracts.cmp8 i c apart _ s state
    {s.regs with rbx := i.storedHigh, rbp := i.queryHigh, rdi := i.storedHigh, rsi := i.queryHigh}
    rfl rfl rfl rfl
  exact high_arguments_execution fetch agree s i.storedHigh i.queryHigh word stored query mapped

theorem ipv4_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) (family : i.family = 32) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (AllowedipsImage.CommonBits.entry+0x6c) s.regs.rbx
        (.ofBitVec (((s.regs.get (.low .rbp .W32)) -
          (scan32 (i.stored32.toBitVec ^^^ i.query32.toBitVec)+1)).setWidth 64)))
      ⟨s, AllowedipsImage.CommonBits.entry+0x51⟩ := by
  obtain ⟨word, mapped⟩ := Option.isSome_iff_exists.mp state.ready.mapped
  obtain ⟨stored, query⟩ := state.words32 family
  let x := i.stored32.toBitVec ^^^ i.query32.toBitVec
  let n := scan32 x+1
  apply callback_step fetch (.ofNat 0xffffffff810f31f0) _ .pc contracts.pc i c apart _ s state
    {s.regs with
      rdx := .ofBitVec (x.setWidth 64), rax := .ofBitVec (n.setWidth 64),
      rbp := .ofBitVec (((s.regs.get (.low .rbp .W32))-n).setWidth 64)}
    rfl rfl rfl rfl
  exact ipv4_scan_execution fetch agree s i.stored32 i.query32 word stored query mapped

theorem seed128_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (apart : i.Separated c)
    (s : MachineData) (state : BodyAt i c s) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (AllowedipsImage.CommonBits.entry+0xb9) s.regs.rbx 0xffffff80)
      ⟨s, AllowedipsImage.CommonBits.entry+0xaf⟩ := by
  obtain ⟨word, mapped⟩ := Option.isSome_iff_exists.mp state.ready.mapped
  apply callback_step fetch (.ofNat 0xffffffff810f31f0) _ .pc contracts.pc i c apart _ s state
    {s.regs with rbp := 0xffffff80} rfl rfl rfl rfl
  exact ipv6_result_seed_execution fetch agree s word mapped

theorem pure_step (fetch : Int64 → Option Decoded)
    (i : Input) (c : CommonBitsCoverage.Context) (initial : MachineState)
    (s : MachineData) (state : BodyAt i c s) (registers : Reg64s) (pc : Int64)
    (sp : registers.rsp = s.regs.rsp) (node : registers.r12 = s.regs.r12)
    (key : registers.r13 = s.regs.r13) (r14 : registers.r14 = s.regs.r14)
    (r15 : registers.r15 = s.regs.r15)
    (region : Eventually (instructionStep fetch) (fun t =>
      t.data.regs = registers ∧ t.data.dmem = s.dmem ∧ t.pc = pc) initial) :
    Eventually (instructionStep fetch) (BodyStep i c s pc registers.rbx registers.rbp) initial := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _ region
  rintro t ⟨regs, memory, atPC⟩
  refine ⟨atPC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact state.same_memory memory (by simpa only [regs] using sp)
      (by simpa only [regs] using node) (by simpa only [regs] using key)
  · simp only [regs]
  · simp only [regs]
  · simpa only [regs] using r14
  · simpa only [regs] using r15
  · intro a outside
    simp only [memory]

theorem guard32_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s) (family : s.regs.get (.low .rbx .W8) = i.family) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (if i.family = 32 then AllowedipsImage.CommonBits.entry+0x4c else
        AllowedipsImage.CommonBits.entry+0x26) s.regs.rbx s.regs.rbp)
      ⟨s, AllowedipsImage.CommonBits.entry+0x21⟩ := by
  apply pure_step fetch i c _ s state s.regs _ rfl rfl rfl rfl rfl
  simpa only [family, beq_iff_eq] using family32_execution fetch agree s

theorem guard128_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s) (family : s.regs.get (.low .rbx .W8) = i.family) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (if i.family = 128 then AllowedipsImage.CommonBits.entry+0x75 else
        AllowedipsImage.CommonBits.entry+0x3e) s.regs.rbx s.regs.rbp)
      ⟨s, AllowedipsImage.CommonBits.entry+0x39⟩ := by
  apply pure_step fetch i c _ s state s.regs _ rfl rfl rfl rfl rfl
  simpa only [family, beq_iff_eq] using family128_execution fetch agree s

theorem guardHigh_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s)
    (stored : s.regs.rbx = i.storedHigh) (query : s.regs.rbp = i.queryHigh) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (if i.storedHigh = i.queryHigh then AllowedipsImage.CommonBits.entry+0xc4 else
        AllowedipsImage.CommonBits.entry+0x93) s.regs.rbx s.regs.rbp)
      ⟨s, AllowedipsImage.CommonBits.entry+0x8e⟩ := by
  apply pure_step fetch i c _ s state s.regs _ rfl rfl rfl rfl rfl
  simpa [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    stored, query, UInt64.toBitVec_inj] using high_equal_execution fetch agree s

theorem high_scan_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (AllowedipsImage.CommonBits.entry+0xaa)
        (.ofBitVec (((scan64 (s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec)).setWidth 32+65).setWidth 64))
        s.regs.rbp)
      ⟨s, AllowedipsImage.CommonBits.entry+0x98⟩ := by
  apply pure_step fetch i c _ s state {s.regs with
    rax := .ofBitVec (s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec),
    rbx := .ofBitVec (((scan64 (s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec)).setWidth 32+65).setWidth 64)}
    _ rfl rfl rfl rfl rfl
  exact high_scan_execution fetch agree s

theorem low_scan_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (state : BodyAt i c s) (family : i.family = 128)
    (equal : i.storedHigh = i.queryHigh) :
    Eventually (instructionStep fetch)
      (BodyStep i c s (AllowedipsImage.CommonBits.entry+0xaa)
        (.ofBitVec (((scan64 (i.storedLow.toBitVec ^^^ i.queryLow.toBitVec)).setWidth 32+1).setWidth 64))
        s.regs.rbp)
      ⟨s, AllowedipsImage.CommonBits.entry+0xc9⟩ := by
  obtain ⟨stored, query⟩ := state.wordsLow family equal
  apply pure_step fetch i c _ s state {s.regs with
    rax := .ofBitVec (i.storedLow.toBitVec ^^^ i.queryLow.toBitVec),
    rbx := .ofBitVec (((scan64 (i.storedLow.toBitVec ^^^ i.queryLow.toBitVec)).setWidth 32+1).setWidth 64)}
    _ rfl rfl rfl rfl rfl
  exact low_scan_execution fetch agree s i.storedLow.toBitVec i.queryLow.toBitVec stored query

end Binary.CommonBits
