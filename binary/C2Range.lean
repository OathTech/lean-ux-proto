import C2CutAssembly
import StackFrame
import CallbackKcovMemory

/-! Work package 2 of result C2: the five segments of the range (`HeadSegment`,
`AdvanceEnters`, `LoopIteration`, `AdvanceStores`, `TailSegment` of `C2CutInterfaces`),
each from the propositions of work package 1 as hypotheses. Brief:
packets/c2/proof/WP2.md.

One file, in parts: `binary/lakefile.toml` registers only the root `C2Range`, lake
resolves no other module of this name prefix, and the lakefile is not this package's
to edit. The parts are marked `Part:` and can be split into modules when roots are
registered for them. -/

/-! Part: a history-keeping `region_eventually`.

The landed `region_eventually` gives an `instructionStep` execution and forgets the
states passed through. The cut predicates need `Quiet` (no state so far at an exit) and
`AtExit.first`, so here the same induction on `LaidOut` is done over `historyStep`,
recording that every state added to the history, the last one apart, is at the address
of an instruction of the region. Generic: nothing here mentions the range. -/
namespace Binary

/-- The addresses of the instructions of a region laid out at `pc`. -/
def regionStarts (pc : Int64) : List (Kraken.Sized Directive) → List Int64
  | [] => []
  | i :: rest => pc :: regionStarts (pc + .ofNat i.size) rest

/-- What a region adds to a history: the states from the start on are `mid` followed by
the final state, and every state of `mid` is at an instruction of the region. -/
def RegionTrail (pc : Int64) (code : List (Kraken.Sized Directive)) (s : MachineState)
    (history : List MachineState) (e : Executed) : Prop :=
  ∃ added mid, e.history = history ++ added ∧ s :: added = mid ++ [e.machine] ∧
    ∀ u ∈ mid, u.pc ∈ regionStarts pc code

/-- Region symbolic execution entails a recorded execution of each fetched instruction,
and the states it records are at the region's instructions. -/
theorem region_history [Labels] {fetch pc code}
    (layout : LaidOut fetch pc code) (s : MachineData) (history : List MachineState)
    (P : MachineState → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d, p⟩)).All P) :
    Eventually (historyStep fetch)
      (fun e => P e.machine ∧ RegionTrail pc code ⟨s, pc⟩ history e) ⟨⟨s, pc⟩, history⟩ := by
  induction layout generalizing s history with
  | nil pc => exact .done _ ⟨run, [], [], by simp, by simp, by simp⟩
  | cons pc i n tail positive here mono rest ih =>
    apply step_cps
    simp only [historyStep, instructionStep, here]
    refine ⟨positive, ?_⟩
    apply mono s ⟨pc, pc + .ofNat n⟩
      (fun d => Directives.interp tail d (pc + .ofNat n) (fun p d => .done ⟨d, p⟩))
      _ (fun p d => .done ⟨d, p⟩) _ P _
    · intro d h
      change Eventually _ _ _
      refine eventually_weaken (historyStep fetch) _ _ _ ?_ (ih d _ h)
      rintro e ⟨post, added, mid, recorded, trail, inside⟩
      refine ⟨post, (⟨d, pc + .ofNat n⟩ : MachineState) :: added, (⟨s, pc⟩ : MachineState) :: mid, ?_, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using recorded
      · simp only [List.cons_append, trail]
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (inside u hu)
    · intro p d h
      change Eventually _ _ _
      exact .done _ ⟨h, [(⟨d, p⟩ : MachineState)], [(⟨s, pc⟩ : MachineState)], rfl, rfl, by
        intro u hu
        rw [List.mem_singleton.mp hu]
        exact List.mem_cons_self⟩
    · exact run

/-- Every state of the history after a region is in the history before it, at an
instruction of the region, or the final state. -/
theorem RegionTrail.mem {pc code s history e} (trail : RegionTrail pc code s history e)
    (u : MachineState) (hu : u ∈ e.history) :
    u ∈ history ∨ u.pc ∈ regionStarts pc code ∨ u = e.machine := by
  obtain ⟨added, mid, recorded, split, inside⟩ := trail
  rw [recorded] at hu
  rcases List.mem_append.mp hu with old | new
  · exact .inl old
  · have : u ∈ mid ++ [e.machine] := split ▸ List.mem_cons_of_mem _ new
    rcases List.mem_append.mp this with m | last
    · exact .inr (.inl (inside u m))
    · exact .inr (.inr (List.mem_singleton.mp last))

/-- Every state of the history after a region but its last is in the history before it
or at an instruction of the region. -/
theorem RegionTrail.mem_dropLast {pc code s history e} (trail : RegionTrail pc code s history e)
    (u : MachineState) (hu : u ∈ e.history.dropLast) :
    u ∈ history ∨ u.pc ∈ regionStarts pc code := by
  obtain ⟨added, mid, recorded, split, inside⟩ := trail
  rw [recorded] at hu
  cases added with
  | nil =>
    rw [List.append_nil] at hu
    exact .inl (List.dropLast_subset _ hu)
  | cons a rest =>
    rw [List.dropLast_append_of_ne_nil (by simp)] at hu
    rcases List.mem_append.mp hu with old | new
    · exact .inl old
    · right
      apply inside
      have drop := congrArg List.dropLast split
      rw [List.dropLast_concat, List.dropLast_cons_of_ne_nil (by simp)] at drop
      rw [← drop]
      exact List.mem_cons_of_mem _ new

#print axioms region_history
#print axioms RegionTrail.mem
#print axioms RegionTrail.mem_dropLast
end Binary

/-! Part: symbolic execution of the non-call instructions of the
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
end Binary.C2

/-! Part: the two ways the range moves between cut points (a
region of ordinary instructions, a call site) with the history kept, and what the
range's own stores do to the carried invariant. -/
namespace Binary.C2
open Binary TrustBase
local instance : Labels := Binary.Image.linkedLabels

/-! ## Moving through the range -/

theorem laidOut_head {fetch : Int64 → Option Decoded} {pc i n tail}
    (layout : LaidOut fetch pc (⟨.instr i, n⟩ :: tail)) : fetch pc = some ⟨i, n⟩ := by
  cases layout; assumption

/-- A region of ordinary instructions, none at an exit: the history stays quiet up to
its last state, and wholly quiet if the final state is not at an exit either. -/
theorem region_step (laid : RegionsLaidOut) {fetch : Int64 → Option Decoded}
    (reading : Reading fetch) (first count : Nat) (bound : first + count ≤ Range.count)
    (safe : ∀ p ∈ regionStarts (regionPC first) (regionCode first count), p ∉ exits)
    (d : MachineData) (history : List MachineState) (quiet : ∀ u ∈ history, u.pc ∉ exits)
    {R : MachineState → Prop} (runs : (run first count d).All R) {Q : Executed → Prop}
    (next : ∀ (t : MachineState) (history' : List MachineState), R t →
      (∀ u ∈ history'.dropLast, u.pc ∉ exits) →
      (t.pc ∉ exits → ∀ u ∈ history', u.pc ∉ exits) →
      Eventually (historyStep fetch) Q ⟨t, history'⟩) :
    Eventually (historyStep fetch) Q ⟨⟨d, regionPC first⟩, history⟩ := by
  apply eventually_trans (historyStep fetch) _ _ _
    (region_history (laid fetch reading.range first count bound) d history R runs)
  rintro ⟨t, history'⟩ ⟨post, trail⟩
  refine next t history' post ?_ ?_
  · intro u hu
    rcases trail.mem_dropLast u hu with old | inside
    · exact quiet u old
    · exact safe _ inside
  · intro final u hu
    rcases trail.mem u hu with old | inside | last
    · exact quiet u old
    · exact safe _ inside
    · rw [last]; exact final

/-- A call site: the callee's rule, then the state at the instruction after the call. -/
theorem call_step {callee : Int64} (site : CallSite callee) (laid : RegionsLaidOut)
    {fetch : Int64 → Option Decoded} {layout : KcovLayout} {preempt : BitVec 32}
    {s0 : MachineState} {kp skb nonce : BitVec 64}
    (reading : Reading fetch) (ctx : Context layout preempt s0 kp skb nonce)
    (k : Nat) (target : Label) (bound : k + 1 ≤ Range.count)
    (code : regionCode k 1 = [⟨.instr (Instrumentation.callInstruction target), 5⟩])
    (named : label target = callee) (after : regionPC k + 5 = regionPC (k + 1))
    (safe : regionPC (k + 1) ∉ exits)
    {w : Window} (d : MachineData) (history : List MachineState)
    (carried : Carried layout preempt kp s0 w d) (quiet : ∀ u ∈ history, u.pc ∉ exits)
    {Q : Executed → Prop}
    (next : ∀ (d' : MachineData) (history' : List MachineState),
      Carried layout preempt kp s0 w d' →
      d'.regs.rbp = d.regs.rbp → d'.regs.r14 = d.regs.r14 → d'.regs.r15 = d.regs.r15 →
      d'.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x10) 8 =
        d.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x10) 8 →
      d'.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x18) 8 =
        d.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x18) 8 →
      (∀ u ∈ history', u.pc ∉ exits) →
      Eventually (historyStep fetch) Q ⟨⟨d', regionPC (k + 1)⟩, history'⟩) :
    Eventually (historyStep fetch) Q ⟨⟨d, regionPC k⟩, history⟩ := by
  have here : fetch (regionPC k) = some ⟨Instrumentation.callInstruction target, 5⟩ :=
    laidOut_head (code ▸ laid fetch reading.range k 1 bound)
  apply eventually_trans (historyStep fetch) _ _ _
    (site fetch layout preempt s0 kp skb nonce w d (regionPC k) target history reading ctx here
      named (after ▸ safe) carried)
  rintro ⟨⟨d', pc'⟩, history'⟩ ⟨at_, c, rbp, r14, r15, s10, s18, q⟩
  dsimp only at at_ c rbp r14 r15 s10 s18
  subst at_
  rw [after]
  exact next d' history' c rbp r14 r15 s10 s18 (q quiet)

/-! ## Memory -/

theorem inRange_at {A b : BitVec 64} {i w n : Nat} {a : BitVec 64}
    (h : InRange A w a) (hA : A = b + .ofNat 64 i) (le : i + w ≤ n) : InRange b n a := by
  subst hA
  obtain ⟨k, hk, e⟩ := h
  exact ⟨i + k, by omega, by rw [e, BitVec.ofNat_add, BitVec.add_assoc]⟩

/-- A store does not change a load from bytes it does not write. -/
theorem load_store_apart (m : Mem 64) (A B : BitVec 64) (wi wj : Nat) (v : Int)
    (apart : ∀ a, InRange A wi a → ¬InRange B wj a) :
    (m.storeInt A wi v).loadInt B wj = m.loadInt B wj :=
  ((storeInt_frame m A wi v).loadInt B wj (fun k hk inside => apart _ inside ⟨k, hk, rfl⟩)).symm

/-- Two fields of one block at disjoint offsets. -/
theorem apart_offsets (base A B : BitVec 64) (i ni j nj : Nat)
    (hA : A = base + .ofNat 64 i) (hB : B = base + .ofNat 64 j)
    (ibound : i + ni ≤ 2 ^ 64) (jbound : j + nj ≤ 2 ^ 64) (apart : i + ni ≤ j ∨ j + nj ≤ i) :
    ∀ a, InRange A ni a → ¬InRange B nj a := by
  subst hA hB
  exact InRange.offset_disjoint base i ni j nj ibound jbound apart

theorem get_store_defined (m : Mem 64) (A : BitVec 64) (k : Nat) (v : Int) (a : BitVec 64)
    (h : (m.get? a).isSome = true) : ((m.storeInt A k v).get? a).isSome = true := by
  have one : (m.loadInt a 1).isSome = true := by
    rw [loadInt_defined]
    intro i hi
    have : i = 0 := by omega
    subst this
    simpa using h
  have stored := storeInt_defined m a A 1 k v one
  rw [loadInt_defined] at stored
  simpa using stored 0 (by omega)

theorem slot10_stack {sp a : BitVec 64} (h : InRange (sp + 0x10) 8 a) : stackBytes sp a := by
  obtain ⟨k, hk, e⟩ := h
  exact .inr ⟨k, by omega, e⟩

theorem slot18_stack {sp a : BitVec 64} (h : InRange (sp + 0x18) 8 a) : stackBytes sp a := by
  obtain ⟨k, hk, e⟩ := h
  exact .inr ⟨8 + k, by omega, by rw [e]; bv_omega⟩

theorem slot10_slot18 (sp : BitVec 64) : ∀ a, InRange (sp + 0x10) 8 a → ¬InRange (sp + 0x18) 8 a :=
  apart_offsets sp _ _ 16 8 24 8 rfl rfl (by omega) (by omega) (by omega)

theorem slot18_slot10 (sp : BitVec 64) : ∀ a, InRange (sp + 0x18) 8 a → ¬InRange (sp + 0x10) 8 a :=
  apart_offsets sp _ _ 24 8 16 8 rfl rfl (by omega) (by omega) (by omega)

/-! ## The window bytes -/

/-- The address of bitmap word `j`, as `WindowAt` writes it. -/
abbrev wordAddress (kp : BitVec 64) (j : Nat) : BitVec 64 :=
  windowBase kp + .ofNat 64 (Layouts.replay_backtrack + j * Layouts.replayWordBytes)

theorem counter_window {kp a : BitVec 64} (h : InRange (kp + 136#64) 8 a) : windowBytes kp a :=
  inRange_at (i := Layouts.keypair_receiving_counter - 136) h (by simp [Layouts.keypair_receiving_counter]) (by decide)

theorem word_window {kp a : BitVec 64} {j : Nat} (hj : j < 128)
    (h : InRange (wordAddress kp j) 8 a) : windowBytes kp a :=
  inRange_at (i := Layouts.replay_backtrack + j * Layouts.replayWordBytes) h rfl
    (by simp only [Layouts.replay_backtrack, Layouts.replayWordBytes, Layouts.replaySize]; omega)

theorem counter_address (kp : BitVec 64) :
    windowBase kp + .ofNat 64 Layouts.replay_counter = kp + 136#64 := by
  simp [windowBase, Layouts.replay_counter, Layouts.keypair_receiving_counter]

/-- The address the image computes for bitmap word `x` (`lea 0x90(%r13,%r14,8)`). -/
theorem word_address (kp x : BitVec 64) :
    kp + 8#64 * x + 144#64 = wordAddress kp x.toNat := by
  simp only [wordAddress, windowBase, Layouts.replay_backtrack, Layouts.replayWordBytes,
    Layouts.keypair_receiving_counter]
  bv_omega

theorem WindowAt.counterLoad {m : Mem 64} {kp : BitVec 64} {w : Window}
    (h : WindowAt m (windowBase kp) w) :
    m.loadInt (kp + 136#64) 8 = some (w.counter.toNat : Int) := by
  rw [← counter_address]; exact h.1

theorem WindowAt.wordLoad {m : Mem 64} {kp : BitVec 64} {w : Window}
    (h : WindowAt m (windowBase kp) w) (j : Nat) (hj : j < 128) :
    m.loadInt (wordAddress kp j) 8 = some ((w.words j).toNat : Int) := h.2 j hj

/-- A store outside the window bytes keeps the window. -/
theorem WindowAt.frame {m : Mem 64} {kp : BitVec 64} {w : Window}
    (h : WindowAt m (windowBase kp) w) (A : BitVec 64) (n : Nat) (v : Int)
    (apart : ∀ a, InRange A n a → ¬windowBytes kp a) :
    WindowAt (m.storeInt A n v) (windowBase kp) w := by
  refine ⟨?_, fun i hi => ?_⟩
  · exact (load_store_apart m A _ n 8 v (fun a inside read => apart a inside
      (counter_window (counter_address kp ▸ read)))).trans h.1
  · exact (load_store_apart m A (wordAddress kp i) n 8 v
      (fun a inside read => apart a inside (word_window hi read))).trans (h.2 i hi)

/-- The store of the counter (`mov %rax,0x88(%r13)`). -/
theorem WindowAt.setCounter {m : Mem 64} {kp : BitVec 64} {w : Window}
    (h : WindowAt m (windowBase kp) w) (v : BitVec 64) :
    WindowAt (m.storeInt (kp + 136#64) 8 v.toInt) (windowBase kp) { w with counter := v } := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [counter_address]; exact load64_store m _ v
  · have bound : i < 128 := hi
    exact (load_store_apart m _ (wordAddress kp i) 8 8 _ (apart_offsets (windowBase kp) _ _ 0 8
      (8 + i * 8) 8 (counter_address kp).symm rfl (by omega) (by omega) (by omega))).trans (h.2 i hi)

/-- A store to bitmap word `j`. -/
theorem WindowAt.setWord {m : Mem 64} {kp : BitVec 64} {w : Window}
    (h : WindowAt m (windowBase kp) w) (j : Nat) (hj : j < 128) (v : BitVec 64) :
    WindowAt (m.storeInt (wordAddress kp j) 8 v.toInt) (windowBase kp)
      { w with words := fun i => if i = j then v else w.words i } := by
  refine ⟨?_, fun i hi => ?_⟩
  · exact (load_store_apart m (wordAddress kp j) _ 8 8 _ (apart_offsets (windowBase kp) _ _
      (8 + j * 8) 8 0 8 rfl rfl (by omega) (by omega) (by omega))).trans h.1
  · have bound : i < 128 := hi
    by_cases same : i = j
    · subst same
      simp only [ite_true]
      exact load64_store m _ v
    · simp only [same, ite_false]
      exact (load_store_apart m (wordAddress kp j) (wordAddress kp i) 8 8 _
        (apart_offsets (windowBase kp) _ _ (8 + j * 8) 8 (8 + i * 8) 8 rfl rfl (by omega)
          (by omega) (by omega))).trans (h.2 i hi)

/-! ## The carried invariant under the range's own steps -/

section
variable {layout : KcovLayout} {preempt : BitVec 32} {s0 : MachineState} {kp skb nonce : BitVec 64}

/-- Register moves that leave the memory and the four kept registers alone. -/
theorem Carried.move {w : Window} {d d' : MachineData} (h : Carried layout preempt kp s0 w d)
    (mem : d'.dmem = d.dmem) (rsp : d'.regs.rsp = d.regs.rsp) (rbx : d'.regs.rbx = d.regs.rbx)
    (r12 : d'.regs.r12 = d.regs.r12) (r13 : d'.regs.r13 = d.regs.r13) :
    Carried layout preempt kp s0 w d' :=
  ⟨mem ▸ h.coverage, mem ▸ h.window, mem ▸ h.stack, mem ▸ h.frame, rsp.trans h.rsp,
    rbx.trans h.rbx, r12.trans h.r12, r13.trans h.r13⟩

/-- A store into a spill slot or the window. -/
theorem Carried.store (ctx : Context layout preempt s0 kp skb nonce) {w w' : Window}
    {d d' : MachineData} (h : Carried layout preempt kp s0 w d) (A : BitVec 64) (n : Nat) (v : Int)
    (foot : ∀ a, InRange A n a → stackBytes s0.data.regs.rsp.toBitVec a ∨ windowBytes kp a)
    (mem : d'.dmem = d.dmem.storeInt A n v)
    (window : WindowAt d'.dmem (windowBase kp) w')
    (rsp : d'.regs.rsp = d.regs.rsp) (rbx : d'.regs.rbx = d.regs.rbx)
    (r12 : d'.regs.r12 = d.regs.r12) (r13 : d'.regs.r13 = d.regs.r13) :
    Carried layout preempt kp s0 w' d' := by
  have written : ∀ a, InRange A n a → Footprint s0.data.regs.rsp.toBitVec kp a := by
    intro a inside
    rcases foot a inside with stack | window
    · exact .inl stack
    · exact .inr (.inl window)
  refine ⟨?_, window, ?_, ?_, rsp.trans h.rsp, rbx.trans h.rbx, r12.trans h.r12, r13.trans h.r13⟩
  · rw [mem]
    apply Kcov.state_frame layout _ _ _ h.coverage (InRange A n) (storeInt_frame _ A n v)
    intro a bytes inside
    rcases bytes with metadata | count | storage
    · exact ctx.coverageApart a (.inl metadata) (written a inside)
    · rcases foot a inside with stack | window
      · exact ctx.stackPreempt a stack count
      · exact ctx.windowPreempt a window count
    · exact ctx.coverageApart a (.inr storage) (written a inside)
  · intro a stack
    rw [mem]
    exact get_store_defined _ _ _ _ _ (h.stack a stack)
  · rw [mem]
    intro a outside
    exact (h.frame a outside).trans
      (storeInt_frame _ A n v a (fun inside => outside (.inl (written a inside))))

end

#print axioms region_step
#print axioms call_step
#print axioms Carried.store
end Binary.C2

/-! Part: the tail of the range (+280 to the exit at +324, call
site 13): the spilled index and counter are reloaded and masked, `bts` tests and sets
the bit, `%esi` gets the unlock argument, `setb` leaves the old bit in `%bpl`. -/
namespace Binary.C2
open Binary TrustBase
local instance : Labels := Binary.Image.linkedLabels

/-- `setBit` with the changed word named once. -/
theorem setBit_eq (w : Window) (t : BitVec 64) :
    setBit w t = Window.mk w.counter (fun i =>
      if i = ((t >>> 6) &&& 127).toNat then
        w.words ((t >>> 6) &&& 127).toNat ||| (1#64 <<< (t &&& 63).toNat)
      else w.words i) := by
  unfold setBit
  congr 1
  funext i
  split
  · rename_i at_; rw [at_]
  · rfl

theorem tail_segment (laid : RegionsLaidOut) (pcSite : PcSite) : TailSegment := by
  intro fetch layout preempt s kp skb nonce w t e reading ctx at_
  obtain ⟨⟨d, pc0⟩, history⟩ := e
  obtain ⟨hpc, carried, quiet, s10, s18⟩ := at_
  dsimp only at hpc carried s10 s18
  subst hpc
  rw [show tailPC = regionPC 61 by decide]
  apply call_step pcSite laid reading ctx 61 "L_ffffffff810f31f0" (by decide) rfl (by decide)
    (by decide) (by decide) d history carried quiet
  intro d1 h1 c1 _ _ _ e10 e18 q1
  have sp1 : d1.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec := by rw [c1.rsp]
  have l18 : d1.dmem.loadInt (d1.regs.rsp.toBitVec + 24#64) 8 = some ((t >>> 6).toNat : Int) := by
    rw [sp1]; exact e18.trans s18
  have l10 : d1.dmem.loadInt (d1.regs.rsp.toBitVec + 16#64) 8 = some (t.toNat : Int) := by
    rw [sp1]; exact e10.trans s10
  apply region_step laid reading 62 2 (by decide) (by decide) d1 h1 q1 (r62 d1 t (t >>> 6) l18 l10)
  rintro ⟨⟨r2, z2, f2, y2, m2⟩, pc2⟩ h2 ⟨hr, hm, hp⟩ - q2
  dsimp only at hr hm hp
  subst hr hm hp
  have q2 := q2 (show regionPC 62 + 5 + 5 ∉ exits by decide)
  rw [show regionPC 62 + 5 + 5 = regionPC 64 by decide]
  apply region_step laid reading 64 1 (by decide) (by decide) _ h2 q2 (r64 _)
  rintro ⟨⟨r3, z3, f3, y3, m3⟩, pc3⟩ h3 ⟨hr, hm, hp⟩ - q3
  dsimp only at hr hm hp
  subst hr hm hp
  have q3 := q3 (show regionPC 64 + 4 ∉ exits by decide)
  rw [show regionPC 64 + 4 = regionPC 65 by decide]
  apply region_step laid reading 65 1 (by decide) (by decide) _ h3 q3 (r65 _)
  rintro ⟨⟨r4, z4, f4, y4, m4⟩, pc4⟩ h4 ⟨hr, hm, hp⟩ - q4
  dsimp only at hr hm hp
  subst hr hm hp
  have q4 := q4 (show regionPC 65 + 4 ∉ exits by decide)
  rw [show regionPC 65 + 4 = regionPC 66 by decide]
  apply region_step laid reading 66 1 (by decide) (by decide) _ h4 q4 (r66 _)
  rintro ⟨⟨r5, z5, f5, y5, m5⟩, pc5⟩ h5 ⟨hr, hm, hp⟩ - q5
  dsimp only at hr hm hp
  subst hr hm hp
  have q5 := q5 (show regionPC 66 + 8 ∉ exits by decide)
  rw [show regionPC 66 + 8 = regionPC 67 by decide]
  have index : ((t >>> 6) &&& 127).toNat < 128 := by
    rw [BitVec.toNat_and, show BitVec.toNat (127 : BitVec 64) = 127 from rfl, and127]; omega
  have offset : (t &&& 63).toNat < 64 := by
    rw [BitVec.toNat_and, show BitVec.toNat (63 : BitVec 64) = 63 from rfl, and63]; omega
  have address : d1.regs.r13.toBitVec + 8#64 * ((t >>> 6) &&& (127 : BitVec 64)) + 144#64 =
      wordAddress kp ((t >>> 6) &&& 127).toNat := by
    rw [c1.r13, ctx.keypair, word_address]
  have word := c1.window.wordLoad _ index
  rw [← address] at word
  apply region_step laid reading 67 1 (by decide) (by decide) _ h5 q5
    (r67 _ (w.words ((t >>> 6) &&& 127).toNat) (by exact offset) (by exact word))
  rintro ⟨⟨r6, z6, f6, y6, m6⟩, pc6⟩ h6 ⟨hr, hm, hcf, hp⟩ - q6
  dsimp only at hr hm hcf hp
  subst hr hm hp
  have q6 := q6 (show regionPC 67 + 4 ∉ exits by decide)
  rw [show regionPC 67 + 4 = regionPC 68 by decide]
  apply region_step laid reading 68 2 (by decide) (by decide) _ h6 q6 (r68 _)
  rintro ⟨d7, pc7⟩ h7 ⟨rsi, rbp, rsp, rbx, r12, r13, hm, hp⟩ first -
  dsimp only at rsi rbp rsp rbx r12 r13 hm hp
  subst hp
  apply Eventually.done
  have window : WindowAt d7.dmem (windowBase kp) (setBit w t) := by
    have stored := c1.window.setWord _ index
      (w.words ((t >>> 6) &&& 127).toNat ||| (1#64 <<< (t &&& 63).toNat))
    rw [← address] at stored
    rw [hm, setBit_eq]
    exact stored
  refine ⟨show regionPC 68 + 5 + 4 = Range.donePC by decide, first, ?_, ?_, fun _ => ?_⟩
  · show accepted ⟨d7, _⟩ = !seen w t
    have old : f6.cf = seen w t := hcf
    simp only [accepted, rbp, old]
    rw [show (regionPC 68 + 5 + 4 == Range.donePC) = true by decide]
    cases seen w t <;> simp
  · exact c1.store ctx _ 8 _ (fun a inside => .inr (word_window index (address ▸ inside))) hm
      window rsp rbx r12 r13
  · show d7.regs.rsi.toNat % 2 ^ 32 = 0x200
    rw [rsi]; rfl

#print axioms tail_segment
end Binary.C2
