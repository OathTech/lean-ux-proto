import C2RangeHistory
import StackFrame
import CallbackKcovMemory

/-! Work package 2 of result C2: symbolic execution of the non-call instructions of the
range, region by region. Each lemma states what one run of consecutive instructions does
to the registers, the memory and the program counter. -/
namespace Binary.C2
open Binary TrustBase Kraken.X64.Parser
local instance : Labels := Binary.Image.linkedLabels

/-- A region of the range executed from its first instruction, falling through or
jumping out. -/
def run (first count : Nat) (s : MachineData) : Effects :=
  Directives.interp (regionCode first count) s (regionPC first) (fun p d => .done ⟨d, p⟩)

theorem store_some (regs zmms status system) (dmem : DataMem) (a : BitVec 64) {w : Width}
    (v : w.type) (ret : MachineData → Effects) (x : Int) (h : dmem.loadInt a w.bytes = some x) :
    MachineData.store ⟨regs, zmms, status, system, dmem⟩ a v ret = require_write_access a w
      (fun _ => ret ⟨regs, zmms, status, system, dmem.storeInt a w.bytes v.toInt⟩) := by
  unfold MachineData.store
  simp only [h]

theorem load_some (regs zmms status system) (dmem : DataMem) (a : BitVec 64) (w : Width)
    (ret : w.type → MachineData → Effects) (x : Int) (h : dmem.loadInt a w.bytes = some x) :
    MachineData.load ⟨regs, zmms, status, system, dmem⟩ a w ret =
      require_read_access a w (fun _ => ret (.ofInt _ x) ⟨regs, zmms, status, system, dmem⟩) := by
  unfold MachineData.load
  simp only [h]

theorem load_some' (s : MachineData) (a : BitVec 64) (w : Width)
    (ret : w.type → MachineData → Effects) (x : Int) (h : s.dmem.loadInt a w.bytes = some x) :
    s.load a w ret = require_read_access a w (fun _ => ret (.ofInt _ x) s) := by
  unfold MachineData.load
  simp only [h]

theorem jump_cancel (a b : Int64) : a + (b - a) = b := by
  apply Int64.toBitVec_inj.mp
  simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
  rw [BitVec.add_comm]
  exact BitVec.sub_add_cancel _ _

theorem sub_zero_iff {w : Nat} (a b : BitVec w) : (a - b = 0#w) = (a = b) := by
  apply propext
  constructor
  · intro h
    have := congrArg (· + b) h
    simpa [BitVec.sub_add_cancel] using this
  · intro h; subst h; simp

syntax "rx_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rx_simp [$ls,*] $[$loc]?) => `(tactic|
    simp [run, Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      RegOrMem.interp, Operand.interp, RelRegOrMem.interp, ConstExpr.interp,
      AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
      BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
      MachineData.set, MachineData.setReg, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      Reg64s.set, Reg64s.set64, BitVec.take, BitVec.drop, Effects.All, Width.bytesv,
      StatusFlags.from_result, CondCode.interp, jump_cancel, sub_zero_iff,
      ShiftCountExpr.interpMasked, ShiftCountExpr.interp, $ls,*] $[$loc]?)

theorem code_62_2 : regionCode 62 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("mov    0x18(%rsp),%r14
mov    0x10(%rsp),%r15")) [5, 5] := rfl

theorem r62 (s : MachineData) (t1 i : BitVec 64)
    (slot18 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24#64) 8 = some (i.toNat : Int))
    (slot10 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16#64) 8 = some (t1.toNat : Int)) :
    (run 62 2 s).All (fun t =>
      t.data.regs = {s.regs with r14 := .ofBitVec i, r15 := .ofBitVec t1} ∧
      t.data.dmem = s.dmem ∧ t.pc = regionPC 62 + 5 + 5) := by
  rx_simp [code_62_2, load_some' (w := .W64) (h := slot18), load_some (w := .W64) (h := slot10)]

theorem code_64_1 : regionCode 64 1 = List.zipWith (fun d n => ⟨d, n⟩) (parse("and    $0x7f,%r14d")) [4] := rfl
theorem code_65_1 : regionCode 65 1 = List.zipWith (fun d n => ⟨d, n⟩) (parse("and    $0x3f,%r15d")) [4] := rfl
theorem code_66_1 : regionCode 66 1 = List.zipWith (fun d n => ⟨d, n⟩) (parse("lea    0x90(%r13,%r14,8),%rax")) [8] := rfl
theorem code_67_1 : regionCode 67 1 = List.zipWith (fun d n => ⟨d, n⟩) (parse("bts    %r15,(%rax)")) [4] := rfl
theorem code_68_2 : regionCode 68 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("mov    $0x200,%esi
setb   %bpl")) [5, 4] := rfl


theorem and127 (n : Nat) : n &&& 127 = n % 128 := Nat.and_two_pow_sub_one_eq_mod n 7
theorem and63 (n : Nat) : n &&& 63 = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6

theorem low32_and127 (x : BitVec 64) :
    (⟨BitVec.setWidth 64 (BitVec.extractLsb' 0 32 x)⟩ : UInt64) &&& 127 = ⟨x &&& 127⟩ := by
  apply UInt64.toBitVec_inj.mp
  show BitVec.setWidth 64 (BitVec.extractLsb' 0 32 x) &&& 127#64 = x &&& 127#64
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  rw [show (127#64).toNat = 127 from rfl, and127, and127]
  simp

theorem low32_and63 (x : BitVec 64) :
    (⟨BitVec.setWidth 64 (BitVec.extractLsb' 0 32 x)⟩ : UInt64) &&& 63 = ⟨x &&& 63⟩ := by
  apply UInt64.toBitVec_inj.mp
  show BitVec.setWidth 64 (BitVec.extractLsb' 0 32 x) &&& 63#64 = x &&& 63#64
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  rw [show (63#64).toNat = 63 from rfl, and63, and63]
  simp

theorem lea8 (x : BitVec 64) : BitVec.ofInt 64 (x.toInt * 8) = 8#64 * x := by
  rw [BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.mul_comm]
  rfl

theorem replaceLow_flag (x : BitVec 64) (b : Bool) :
    (x.replaceLow (BitVec.ofNat 8 b.toNat)).toNat % 256 = if b = true then 1 else 0 := by
  unfold BitVec.replaceLow
  rw [BitVec.toNat_setWidth]
  change (x.drop 8 ++ BitVec.ofNat 8 b.toNat).toNat % 2 ^ 64 % 256 = _
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq]
  cases b <;> simp <;> omega

theorem r64 (s : MachineData) :
    (run 64 1 s).All (fun t =>
      t.data.regs = {s.regs with r14 := .ofBitVec (s.regs.r14.toBitVec &&& 127)} ∧
      t.data.dmem = s.dmem ∧ t.pc = regionPC 64 + 4) := by
  rx_simp [code_64_1, low32_and127]

theorem r65 (s : MachineData) :
    (run 65 1 s).All (fun t =>
      t.data.regs = {s.regs with r15 := .ofBitVec (s.regs.r15.toBitVec &&& 63)} ∧
      t.data.dmem = s.dmem ∧ t.pc = regionPC 65 + 4) := by
  rx_simp [code_65_1, low32_and63]

theorem r66 (s : MachineData) :
    (run 66 1 s).All (fun t =>
      t.data.regs = {s.regs with rax := s.regs.r13 + 8 * s.regs.r14 + 144} ∧
      t.data.dmem = s.dmem ∧ t.pc = regionPC 66 + 8) := by
  rx_simp [code_66_1]
  apply UInt64.toBitVec_inj.mp
  exact lea8 _

theorem r67 (s : MachineData) (word : BitVec 64) (off : s.regs.r15.toNat < 64)
    (load : s.dmem.loadInt s.regs.rax.toBitVec 8 = some (word.toNat : Int)) :
    (run 67 1 s).All (fun t =>
      t.data.regs = s.regs ∧
      t.data.dmem = s.dmem.storeInt s.regs.rax.toBitVec 8 (word ||| (1#64 <<< s.regs.r15.toNat)).toInt ∧
      t.data.status.cf = word.getLsbD s.regs.r15.toNat ∧
      t.pc = regionPC 67 + 4) := by
  rx_simp [code_67_1, load, off, Nat.not_le.mpr off, show (Width.W64 != Width.W64) = false from rfl]

theorem r68 (s : MachineData) :
    (run 68 2 s).All (fun t =>
      t.data.regs.rsi = 0x200 ∧ t.data.regs.rbp.toNat % 256 = (if s.status.cf then 1 else 0) ∧
      t.data.regs.rsp = s.regs.rsp ∧ t.data.regs.rbx = s.regs.rbx ∧ t.data.regs.r12 = s.regs.r12 ∧
      t.data.regs.r13 = s.regs.r13 ∧
      t.data.dmem = s.dmem ∧ t.pc = regionPC 68 + 5 + 4) := by
  rx_simp [code_68_2, replaceLow_flag]

/-! ### The advance path -/

theorem code_59_2 : regionCode 59 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("mov    0x10(%rsp),%rax
mov    %rax,0x88(%r13)")) [5, 7] := rfl

theorem r59 (s : MachineData) (t1 : BitVec 64) (x : Int)
    (slot10 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16#64) 8 = some (t1.toNat : Int))
    (counter : s.dmem.loadInt (s.regs.r13.toBitVec + 136#64) 8 = some x) :
    (run 59 2 s).All (fun t =>
      t.data.regs = {s.regs with rax := .ofBitVec t1} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.r13.toBitVec + 136#64) 8 t1.toInt ∧
      t.pc = regionPC 59 + 5 + 7) := by
  rx_simp [code_59_2, load_some' (w := .W64) (h := slot10), store_some (w := .W64) (h := counter)]

/-- Byte offset of bitmap word `x & 127` from the first word. Kept opaque to `simp`. -/
def wordOff (x : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (8 * (x &&& 127).toNat)

theorem wordOff_nat (n : Nat) :
    BitVec.ofInt 64 ((↑(n % 4294967296 % 18446744073709551616 &&& 127) : Int).bmod
      18446744073709551616 * 8) = BitVec.ofNat 64 (8 * (n % 128)) := by
  have h : n % 4294967296 % 18446744073709551616 &&& 127 = n % 128 := by
    rw [and127]; omega
  rw [h]
  have b : ((↑(n % 128) : Int)).bmod 18446744073709551616 = ↑(n % 128) := by
    rw [Int.bmod_def]; split <;> omega
  rw [b, show ((↑(n % 128) : Int) * 8) = ((8 * (n % 128) : Nat) : Int) by omega, BitVec.ofInt_natCast]

theorem wordOff_eq (x : BitVec 64) : wordOff x = BitVec.ofNat 64 (8 * (x.toNat % 128)) := by
  unfold wordOff
  rw [BitVec.toNat_and, show BitVec.toNat (127 : BitVec 64) = 127 from rfl, and127]

theorem wordOff_sum (a b : UInt64) :
    BitVec.ofInt 64 ((↑((a.toNat + b.toNat) % 4294967296 % 18446744073709551616 &&& 127) : Int).bmod
      18446744073709551616 * 8) = wordOff (a.toBitVec + b.toBitVec) := by
  rw [wordOff_nat, wordOff_eq, BitVec.toNat_add]
  congr 2
  simp only [UInt64.toNat_toBitVec]
  omega

theorem wordOff_nat' (n : Nat) :
    BitVec.ofInt 64 ((↑(n % 18446744073709551616 &&& 127) : Int).bmod
      18446744073709551616 * 8) = BitVec.ofNat 64 (8 * (n % 128)) := by
  have h : n % 18446744073709551616 &&& 127 = n % 128 := by
    rw [and127]; omega
  rw [h]
  have b : ((↑(n % 128) : Int)).bmod 18446744073709551616 = ↑(n % 128) := by
    rw [Int.bmod_def]; split <;> omega
  rw [b, show ((↑(n % 128) : Int) * 8) = ((8 * (n % 128) : Nat) : Int) by omega, BitVec.ofInt_natCast]

theorem wordOff_sum' (a b : UInt64) :
    BitVec.ofInt 64 ((↑((a.toNat + b.toNat) % 18446744073709551616 &&& 127) : Int).bmod
      18446744073709551616 * 8) = wordOff (a.toBitVec + b.toBitVec) := by
  rw [wordOff_nat', wordOff_eq, BitVec.toNat_add]
  congr 2
  simp only [UInt64.toNat_toBitVec]
  omega

theorem code_49_6 : regionCode 49 6 = List.zipWith (fun d n => ⟨d, n⟩) (parse("lea    (%r14,%rbp,1),%rax
add    $0x1,%rbp
mov    %r15,%rdi
and    $0x7f,%eax
mov    %rbp,%rsi
movq   $0x0,0x90(%r13,%rax,8)")) [4, 4, 3, 3, 3, 12] := rfl

theorem r49 (s : MachineData) (x : Int)
    (word : s.dmem.loadInt (s.regs.r13.toBitVec + wordOff (s.regs.r14.toBitVec + s.regs.rbp.toBitVec) + 144#64) 8 = some x) :
    (run 49 6 s).All (fun t =>
      t.data.regs = {s.regs with rax := .ofBitVec ((s.regs.r14.toBitVec + s.regs.rbp.toBitVec) &&& 127), rbp := 1 + s.regs.rbp, rdi := s.regs.r15, rsi := 1 + s.regs.rbp} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.r13.toBitVec + wordOff (s.regs.r14.toBitVec + s.regs.rbp.toBitVec) + 144#64) 8 0 ∧
      t.pc = regionPC 49 + 4 + 4 + 3 + 3 + 3 + 12) := by
  rx_simp [code_49_6, wordOff_sum, wordOff_sum', low32_and127, store_some (w := .W64) (h := word)]

/-! Compare-and-branch regions: registers and memory unchanged. -/
def BranchPost (s : MachineData) (pc : Int64) (t : MachineState) : Prop :=
  t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧ t.pc = pc

macro "rx_branch" : tactic => `(tactic| (
  split <;> rename_i hspec <;> split <;> rename_i hcond <;>
  (show _ = _ ∧ _ = _ ∧ _ = _) <;> refine ⟨rfl, rfl, ?_⟩ <;>
  first
    | rfl
    | (show label _ = _; decide)
    | (exfalso
       simp only [← UInt64.toNat_toBitVec, limit] at hcond hspec
       try simp only [Width.bits] at hcond hspec
       bv_omega)))

theorem code_56_2 : regionCode 56 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("cmp    %rbp,%r15
jae L_ffffffff8139d381")) [3, 2] := rfl

theorem r56 (s : MachineData) :
    (run 56 2 s).All (BranchPost s
      (if s.regs.rbp.toBitVec ≤ s.regs.r15.toBitVec then regionPC 48 else regionPC 56 + 3 + 2)) := by
  rx_simp [code_56_2, Callback.no_borrow_iff]
  rx_branch

theorem code_34_11 : regionCode 34 11 = List.zipWith (fun d n => ⟨d, n⟩) (parse("mov    %rbp,%r14
mov    %r15,%rcx
mov    $0x80,%eax
shr    $0x6,%r14
mov    %rcx,%rdi
mov    %rcx,0x18(%rsp)
mov    $0x1,%ebp
sub    %r14,%r15
mov    %r14,%rsi
cmp    %rax,%r15
cmova  %rax,%r15")) [3, 3, 5, 4, 3, 5, 5, 3, 3, 3, 4] := rfl

theorem r34 (s : MachineData) (x : Int)
    (slot18 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24#64) 8 = some x) :
    (run 34 11 s).All (fun t =>
      t.data.regs = {s.regs with r14 := s.regs.rbp >>> 6, rcx := s.regs.r15, rax := 0x80, rdi := s.regs.r15, rbp := 1, rsi := s.regs.rbp >>> 6, r15 := .ofBitVec (if 128#64 < s.regs.r15.toBitVec - s.regs.rbp.toBitVec >>> 6 then 128#64 else s.regs.r15.toBitVec - s.regs.rbp.toBitVec >>> 6)} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec + 24#64) 8 s.regs.r15.toBitVec.toInt ∧
      t.pc = regionPC 34 + 3 + 3 + 5 + 4 + 3 + 5 + 5 + 3 + 3 + 3 + 4) := by
  rx_simp [code_34_11, store_some (w := .W64) (h := slot18), Callback.no_borrow_iff]
  have h128 : UInt64.toNat (OfNat.ofNat 128) = 128 := rfl
  rw [h128]
  split <;> rename_i hcond <;> split <;> rename_i hspec <;>
  first
    | rfl
    | (exfalso
       simp only [← UInt64.toNat_toBitVec] at hcond hspec
       bv_omega)

theorem code_46_2 : regionCode 46 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("cmp    %r14,0x18(%rsp)
je L_ffffffff8139d3ad")) [5, 2] := rfl

theorem r46 (s : MachineData) (i : BitVec 64)
    (slot18 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24#64) 8 = some (i.toNat : Int)) :
    (run 46 2 s).All (BranchPost s
      (if i = s.regs.r14.toBitVec then regionPC 58 else regionPC 46 + 5 + 2)) := by
  rx_simp [code_46_2, load_some' (w := .W64) (h := slot18)]
  split <;> (show _ = _ ∧ _ = _ ∧ _ = _) <;> refine ⟨rfl, rfl, ?_⟩ <;>
  first
    | rfl
    | (show label _ = _; decide)

/-! ### The head -/

theorem code_0_5 : regionCode 0 5 = List.zipWith (fun d n => ⟨d, n⟩) (parse("mov    0x28(%rbx),%r14
addl   $0x200,0x92b314(%rip)
mov    0x88(%r13),%rbp
mov    $0xffffffffffffe03e,%rdi
mov    %rbp,%rsi")) [4, 10, 7, 7, 3] := rfl

theorem regionPC_zero : regionPC 0 = Range.entry := by decide

theorem r0 (s : MachineData) (th c : BitVec 64) (p : BitVec 32)
    (theirs : s.dmem.loadInt (s.regs.rbx.toBitVec + 40#64) 8 = some (th.toNat : Int))
    (preempt : s.dmem.loadInt preemptCountAddress 4 = some (p.toNat : Int))
    (counter : (s.dmem.storeInt preemptCountAddress 4 (0x200 + p).toInt).loadInt
      (s.regs.r13.toBitVec + 136#64) 8 = some (c.toNat : Int)) :
    (run 0 5 s).All (fun t =>
      t.data.regs = {s.regs with r14 := .ofBitVec th, rbp := .ofBitVec c, rdi := 0xffffffffffffe03e, rsi := .ofBitVec c} ∧
      t.data.dmem = s.dmem.storeInt preemptCountAddress 4 (0x200 + p).toInt ∧
      t.pc = Range.entry + 0x1f) := by
  rx_simp [preemptCountAddress] at preempt counter
  rx_simp [code_0_5, regionPC_zero, Range.entry, preemptCountAddress, load_some' (w := .W64) (h := theirs),
    load_some (w := .W32) (h := preempt), store_some (w := .W32) (h := preempt),
    load_some (w := .W64) (h := counter)]

theorem code_6_2 : regionCode 6 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("cmp    $0xffffffffffffe03e,%rbp
ja L_ffffffff8139d80d")) [7, 6] := rfl

theorem r6 (s : MachineData) :
    (run 6 2 s).All (BranchPost s
      (if limit < s.regs.rbp.toBitVec then Range.rejectWindowPC else regionPC 6 + 7 + 6)) := by
  rx_simp [code_6_2, Callback.no_borrow_iff]
  rx_branch

theorem code_9_2 : regionCode 9 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("mov    %r14,%rsi
mov    $0xffffffffffffe03d,%rdi")) [3, 7] := rfl

theorem r9 (s : MachineData) :
    (run 9 2 s).All (fun t =>
      t.data.regs = {s.regs with rsi := s.regs.r14, rdi := 0xffffffffffffe03d} ∧
      t.data.dmem = s.dmem ∧ t.pc = regionPC 9 + 3 + 7) := by
  rx_simp [code_9_2]

theorem code_12_2 : regionCode 12 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("cmp    $0xffffffffffffe03d,%r14
ja L_ffffffff8139d9c3")) [7, 6] := rfl

theorem r12 (s : MachineData) :
    (run 12 2 s).All (BranchPost s
      (if limit ≤ s.regs.r14.toBitVec then Range.rejectLimitPC else regionPC 12 + 7 + 6)) := by
  rx_simp [code_12_2, Callback.no_borrow_iff]
  rx_branch

theorem code_15_5 : regionCode 15 5 = List.zipWith (fun d n => ⟨d, n⟩) (parse("lea    0x1(%r14),%rax
add    $0x1fc1,%r14
mov    %rbp,%rdi
mov    %r14,%rsi
mov    %rax,0x10(%rsp)")) [4, 7, 3, 3, 5] := rfl

theorem r15 (s : MachineData) (x : Int)
    (slot10 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16#64) 8 = some x) :
    (run 15 5 s).All (fun t =>
      t.data.regs = {s.regs with rax := s.regs.r14 + 1, r14 := s.regs.r14 + 0x1fc1, rdi := s.regs.rbp, rsi := s.regs.r14 + 0x1fc1} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec + 16#64) 8 (s.regs.r14.toBitVec + 1#64).toInt ∧
      t.pc = regionPC 15 + 4 + 7 + 3 + 3 + 5) := by
  rx_simp [code_15_5, store_some (w := .W64) (h := slot10)]
  exact UInt64.add_comm _ _

theorem code_21_2 : regionCode 21 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("cmp    %rbp,%r14
jb L_ffffffff8139d80d")) [3, 6] := rfl

theorem r21 (s : MachineData) :
    (run 21 2 s).All (BranchPost s
      (if s.regs.r14.toBitVec < s.regs.rbp.toBitVec then Range.rejectWindowPC else regionPC 21 + 3 + 6)) := by
  rx_simp [code_21_2, Callback.no_borrow_iff]
  rx_branch

theorem code_24_6 : regionCode 24 6 = List.zipWith (fun d n => ⟨d, n⟩) (parse("mov    0x10(%rsp),%r14
mov    %rbp,%rdi
mov    %r14,%r15
mov    %r14,%rsi
shr    $0x6,%r15
mov    %r15,0x18(%rsp)")) [5, 3, 3, 3, 4, 5] := rfl

theorem r24 (s : MachineData) (t1 : BitVec 64) (x : Int)
    (slot10 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16#64) 8 = some (t1.toNat : Int))
    (slot18 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24#64) 8 = some x) :
    (run 24 6 s).All (fun t =>
      t.data.regs = {s.regs with r14 := .ofBitVec t1, rdi := s.regs.rbp, r15 := .ofBitVec (t1 >>> 6), rsi := .ofBitVec t1} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec + 24#64) 8 (t1 >>> 6).toInt ∧
      t.pc = regionPC 24 + 5 + 3 + 3 + 3 + 4 + 5) := by
  rx_simp [code_24_6, load_some' (w := .W64) (h := slot10), store_some (w := .W64) (h := slot18)]

theorem code_31_2 : regionCode 31 2 = List.zipWith (fun d n => ⟨d, n⟩) (parse("cmp    %r14,%rbp
jae L_ffffffff8139d3be")) [3, 2] := rfl

theorem r31 (s : MachineData) :
    (run 31 2 s).All (BranchPost s
      (if s.regs.rbp.toBitVec < s.regs.r14.toBitVec then regionPC 31 + 3 + 2 else regionPC 61)) := by
  rx_simp [code_31_2, Callback.no_borrow_iff]
  rx_branch
end Binary.C2
