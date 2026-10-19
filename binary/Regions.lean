import Image
import Execution
import ImageLayout
import Kraken.X64.OmniSemantics
import Kraken.X64.Sep

namespace Binary.Lookup

local instance : Labels := Image.linkedLabels

def run (code : List (Kraken.Sized Directive)) (offset : Nat) (s : MachineData) : Effects :=
  Directives.interp code s (Image.Lookup.entry + .ofNat offset) (fun p d => .done ⟨d, p⟩)

private theorem compare_nat (a b : BitVec 32) :
    (a - b == 0#32) = (a.toNat == b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add, BitVec.toNat_inj]

private theorem u64_zero (v : UInt64) : v.toBitVec = 0#64 ↔ v = 0 := by
  exact UInt64.toBitVec_inj

def callMemory (s : MachineData) (returnOffset : Nat) : DataMem :=
  s.dmem.storeInt (s.regs.rsp.toBitVec - 8) 8
    (Image.Lookup.entry + .ofNat returnOffset).toBitVec.toInt

/-- All singleton trace-PC regions have this same instruction term. -/
theorem trace_call (offset : Nat) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.Lookup.r34 offset s).All (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (offset + 5) ∧ t.pc = .ofNat 0xffffffff810f31f0) := by
  simp [run, Image.Lookup.r34, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, MachineData.store,
    Reg64s.get64, Reg64s.set64, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory]
  simp_all [Effects.All,  Int64.add_assoc]
  constructor
  · simp [Int.add_assoc]
  · have cancel (a b : Int64) : a + (b - a) = b := by
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm]
      exact BitVec.sub_add_cancel _ _
    simpa only [Int64.add_assoc] using
      (cancel (Image.Lookup.entry + Int64.ofNat offset + 5)
        (label "L_ffffffff810f31f0")).trans (show label "L_ffffffff810f31f0" =
          (-2129710608 : Int64) from by decide)

theorem trace_region_terms :
    Image.Lookup.r47 = Image.Lookup.r34 ∧ Image.Lookup.r5e = Image.Lookup.r34 ∧
    Image.Lookup.r6c = Image.Lookup.r34 ∧ Image.Lookup.r73 = Image.Lookup.r34 ∧
    Image.Lookup.r95 = Image.Lookup.r34 ∧ Image.Lookup.rad = Image.Lookup.r34 ∧
    Image.Lookup.rc5 = Image.Lookup.r34 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The container_of subtraction and the following real CALL. The pushed
    return address is part of memory, not an assumed control-flow shortcut. -/
theorem container_entry (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.Lookup.r39 0x39 s).All (fun t =>
      t.data.regs = {s.regs with rbx := s.regs.rbx - 8, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x42 ∧ t.pc = .ofNat 0xffffffff810f31f0) := by
  simp [run, Image.Lookup.r39, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory, Image.Lookup.entry]
  simp_all [Effects.All]
  rfl

theorem index_load (s : MachineData) (index : UInt32) (stackWord : Int)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec + 28) 4 = some index.toNat)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.Lookup.r4c 0x4c s).All (fun t =>
      t.data.regs = {s.regs with
        rbp := .ofNat index.toNat, rdi := .ofNat index.toNat,
        rsi := .ofNat ((s.regs.get (.low .r12 .W32)).toNat), rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x59 ∧ t.pc = .ofNat 0xffffffff810f4080) := by
  simp [run, Image.Lookup.r4c, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.drop, BitVec.take,
    RelRegOrMem.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    Effects.All, Width.bytesv,   callMemory, Image.Lookup.entry]
  simp_all [Effects.All]
  refine ⟨⟨?_, ?_⟩, by rfl⟩
  all_goals apply UInt64.toBitVec_inj.mp
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp

theorem peer_argument (s : MachineData) (peer : UInt64) (stackWord : Int)
    (field : s.dmem.loadInt s.regs.rbx.toBitVec 8 = some peer.toNat)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.Lookup.rb2 0xb2 s).All (fun t =>
      t.data.regs = {s.regs with rdi := peer, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0xba ∧ t.pc = Image.PeerGet.entry) := by
  simp [run, Image.Lookup.rb2, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp,  Reg64s.get64,
    Reg64s.set, Reg64s.set64,  BitVec.take,
    RelRegOrMem.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
     BitVec.ofInt_toInt,
    Effects.All, Width.bytesv, field,  callMemory, Image.Lookup.entry]
  simp_all [Effects.All]
  rfl

theorem type_mask (s : MachineData) (kind : UInt32) (stackWord : Int)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec + 24) 4 = some kind.toNat)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.Lookup.r9a 0x9a s).All (fun t =>
      let masked := (s.regs.get (.low .r14 .W32)) &&& kind.toBitVec
      t.data.regs = {s.regs with
        r14 := .ofNat masked.toNat, rsi := .ofNat masked.toNat,
        rdi := 0, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0xa8 ∧ t.pc = .ofNat 0xffffffff810f4100) := by
  simp [run, Image.Lookup.r9a, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.drop, BitVec.take,
    RelRegOrMem.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    Effects.All, Width.bytesv,   callMemory, Image.Lookup.entry]
  simp_all [Effects.All]
  refine ⟨⟨?_, ?_⟩, by rfl⟩
  all_goals apply UInt64.toBitVec_inj.mp
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp
  have bound : (s.regs.r14.toNat % 4294967296 % 18446744073709551616 &&& kind.toNat) ≤
      kind.toNat := Nat.and_le_right
  have small := kind.toNat_lt_size
  change kind.toNat < 4294967296 at small
  omega

theorem bh_arguments (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.Lookup.r78 0x78 s).All (fun t =>
      t.data.regs = {s.regs with
        rdi := (Image.Lookup.entry + 0x84).toUInt64, rsi := 512, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x89 ∧ t.pc = .ofNat 0xffffffff810732c0) := by
  simp [run, Image.Lookup.r78, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp,  Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp,  Reg64s.get64,
    Reg64s.set, Reg64s.set64,
    RelRegOrMem.interp, ConstExpr.interp,

    Effects.All, Width.bytesv,  callMemory, Image.Lookup.entry]
  simp_all [Effects.All]
  exact ⟨by decide, by rfl⟩

/-- The decoded index comparison, with unchanged heap and registers. -/
theorem index_compare (s : MachineData) :
    (run Image.Lookup.r59 0x59 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if (s.regs.get (.low .rbp .W32)).toNat ==
                (s.regs.get (.low .r12 .W32)).toNat
        then Image.Lookup.entry + 0x95 else Image.Lookup.entry + 0x5e) := by
  simp [run, Image.Lookup.r59, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp, compare_nat]
  split <;> simp_all [Effects.All, Image.Lookup.entry] <;> rfl

/-- The loop's entry-address null guard after container_of. -/
theorem entry_guard (s : MachineData) :
    (run Image.Lookup.r42 0x42 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbx .W64) == 0 then
        Image.Lookup.entry + 0x71 else Image.Lookup.entry + 0x47) := by
  simp [run, Image.Lookup.r42, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp]
  by_cases h : s.regs.get (.low .rbx .W64) = 0#64
  all_goals simp_all [Effects.All, Image.Lookup.entry]
  rfl

/-- The compiler's type-mask decision. Nonzero represents membership. -/
theorem type_guard (s : MachineData) :
    (run Image.Lookup.ra8 0xa8 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .r14 .W32) == 0 then
        Image.Lookup.entry + 0x71 else Image.Lookup.entry + 0xad) := by
  simp [run, Image.Lookup.ra8, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp]
  by_cases h : s.regs.get (.low .r14 .W32) = 0#32
  all_goals simp_all [Effects.All, Image.Lookup.entry]
  rfl

/-- The shared miss exit sets the return-entry register to NULL. -/
theorem clear_entry (s : MachineData) :
    (run Image.Lookup.r71 0x71 s).All (fun t =>
      t.data.regs = {s.regs with rbx := 0} ∧ t.data.dmem = s.dmem ∧
      t.pc = Image.Lookup.entry + 0x73) := by
  simp [run, Image.Lookup.r71, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, MachineData.set, MachineData.setReg, Reg64s.set,
    Reg64s.set64, Image.Lookup.entry]

/-- One complete bucket-loop back edge. The next pointer is read from the
    DWARF field at +8; all other bytes and registers are preserved. -/
theorem next_entry (s : MachineData) (next : UInt64)
    (h : s.dmem.loadInt (s.regs.rbx.toBitVec + 8) 8 = some next.toNat) :
    (run Image.Lookup.r63 0x63 s).All (fun t =>
      t.data.regs = {s.regs with rbx := next} ∧ t.data.dmem = s.dmem ∧
      t.pc = if next = 0 then Image.Lookup.entry + 0x6c else Image.Lookup.entry + 0x34) := by
  simp [run, Image.Lookup.r63, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, AddrExpr.interp, ConstExpr.interp,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
    Effects.All, StatusFlags.from_result, CondCode.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64, BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_add,
    BitVec.ofInt_toInt, BitVec.ofInt_ofNat]
  by_cases hz : next = 0
  all_goals simp_all [Effects.All, Image.Lookup.entry, u64_zero]
  rfl

/-- The return from peer-get is stored even when it is NULL. Separation
    preserves the rest of the heap exactly, without a callee assumption. -/
theorem peer_write (s : MachineData) (old : List UInt8) (frame : DataMem → Prop)
    (mem : s.dmem =⋆ Eq (old.At s.regs.rbx.toBitVec) ⋆ frame)
    (len : old.length = 8) :
    (run Image.Lookup.rba 0xba s).All (fun t =>
      t.data.regs = {s.regs with rbp := s.regs.rax} ∧
      (t.data.dmem =⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At s.regs.rbx.toBitVec) ⋆ frame) ∧
      t.pc = if s.regs.rax = 0 then Image.Lookup.entry + 0x71 else Image.Lookup.entry + 0xc5) := by
  have load := Mem.loadInt_sep old s.regs.rbx.toBitVec 8 frame s.dmem mem len (by decide)
  have store := Mem.storeInt_sep s.regs.rbx.toBitVec 8 old frame s.dmem ⟨mem, len⟩ s.regs.rax.toBitVec.toInt
  simp [run, Image.Lookup.rba, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, AddrExpr.interp, ConstExpr.interp,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
    Effects.All, StatusFlags.from_result, CondCode.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
    BitVec.toAddressSize, BitVec.signed,  BitVec.ofInt_toInt,
     load]
  by_cases hz : s.regs.rax = 0
  all_goals simp_all [Effects.All, Image.Lookup.entry, u64_zero]
  rfl

/-- On success, write only the caller's peer-output slot. -/
theorem output_write (s : MachineData) (old : List UInt8) (frame : DataMem → Prop)
    (mem : s.dmem =⋆ Eq (old.At s.regs.r13.toBitVec) ⋆ frame)
    (len : old.length = 8) :
    (run Image.Lookup.rca 0xca s).All (fun t =>
      t.data.regs = s.regs ∧
      (t.data.dmem =⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At s.regs.r13.toBitVec) ⋆ frame) ∧
      t.pc = Image.Lookup.entry + 0x73) := by
  have load := Mem.loadInt_sep old s.regs.r13.toBitVec 8 frame s.dmem mem len (by decide)
  have store := Mem.storeInt_sep s.regs.r13.toBitVec 8 old frame s.dmem ⟨mem, len⟩ s.regs.rbp.toBitVec.toInt
  simp [run, Image.Lookup.rca, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
    Effects.All, MachineData.set,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt, load, store]
  rfl

/-- The problematic dead-peer path, as a kernel-checked instruction fact:
    a NULL return from peer-get overwrites the original pointer with NULL. -/
theorem dead_peer_clears_pointer (s : MachineData) (old : List UInt8)
    (frame : DataMem → Prop)
    (mem : s.dmem =⋆ Eq (old.At s.regs.rbx.toBitVec) ⋆ frame)
    (len : old.length = 8) (dead : s.regs.rax = 0) :
    (run Image.Lookup.rba 0xba s).All (fun t =>
      t.data.dmem.loadInt s.regs.rbx.toBitVec 8 = some 0 ∧
      t.pc = Image.Lookup.entry + 0x71) := by
  apply all_mono _ _ _ _ (peer_write s old frame mem len)
  rintro t ⟨_, hm, hp⟩
  have hz : s.regs.rax.toBitVec.toInt = 0 := by simp [dead]
  rw [hz] at hm
  have hl := Mem.loadInt_sep (Int.toBytes 8 0) s.regs.rbx.toBitVec 8 frame t.data.dmem hm
    (Int.toBytes_length 8 0) (by decide)
  exact ⟨hl, by simpa [dead] using hp⟩

/-- Restore the five saved registers and return to the saved entry frame.
    No exit-range convention replaces RET; its stack load is interpreted. -/
theorem epilogue (s : MachineData) (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec + 32) 8 = some r14.toNat)
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec + 40) 8 = some ra.toNat) :
    (run Image.Lookup.r89 0x89 s).All (fun t =>
      t.data.regs = {s.regs with
        rax := s.regs.rbx, rbx := bx, rbp := bp, r12, r13, r14, rsp := s.regs.rsp + 48} ∧
      t.data.dmem = s.dmem ∧ t.pc = .ofBitVec ra.toBitVec) := by
  simp [run, Image.Lookup.r89, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
     h0,    ]
  simp_all [Effects.All,  ]
  apply Int64.toBitVec_inj.mp
  simp

#print axioms epilogue
#print axioms trace_call
#print axioms trace_region_terms
#print axioms container_entry
#print axioms index_load
#print axioms peer_argument
#print axioms type_mask
#print axioms bh_arguments
#print axioms dead_peer_clears_pointer
#print axioms output_write
#print axioms peer_write
#print axioms next_entry
#print axioms index_compare
#print axioms entry_guard
#print axioms type_guard
#print axioms clear_entry

end Binary.Lookup
