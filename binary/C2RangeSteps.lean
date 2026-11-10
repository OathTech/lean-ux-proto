import C2RangeRegions

/-! Work package 2 of result C2: the two ways the range moves between cut points (a
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

/-- The address the clear loop computes for bitmap word `x & 127`
(`movq $0x0,0x90(%r13,%rax,8)`). -/
theorem wordOff_address (kp x : BitVec 64) :
    kp + wordOff x + 144#64 = wordAddress kp (x &&& 127).toNat := by
  simp only [wordAddress, windowBase, Layouts.replay_backtrack, Layouts.replayWordBytes,
    Layouts.keypair_receiving_counter, wordOff]
  bv_omega

theorem and127_lt (x : BitVec 64) : (x &&& 127).toNat < 128 := by
  rw [BitVec.toNat_and, show BitVec.toNat (127 : BitVec 64) = 127 from rfl, and127]; omega

theorem and63_lt (x : BitVec 64) : (x &&& 63).toNat < 64 := by
  rw [BitVec.toNat_and, show BitVec.toNat (63 : BitVec 64) = 63 from rfl, and63]; omega

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

/-- A store into the window keeps a load from the stack slots. -/
theorem window_store_slot (ctx : Context layout preempt s0 kp skb nonce) (m : Mem 64)
    (A B : BitVec 64) (n : Nat) (v : Int) (inWindow : ∀ a, InRange A n a → windowBytes kp a)
    (inStack : ∀ a, InRange B 8 a → stackBytes s0.data.regs.rsp.toBitVec a) :
    (m.storeInt A n v).loadInt B 8 = m.loadInt B 8 :=
  load_store_apart m A B n 8 v (fun a ia ib => ctx.stackWindow a (inStack a ib) (inWindow a ia))

/-- A store into the stack slots keeps the window. -/
theorem WindowAt.stackStore (ctx : Context layout preempt s0 kp skb nonce) {m : Mem 64}
    {w : Window} (h : WindowAt m (windowBase kp) w) (A : BitVec 64) (n : Nat) (v : Int)
    (inStack : ∀ a, InRange A n a → stackBytes s0.data.regs.rsp.toBitVec a) :
    WindowAt (m.storeInt A n v) (windowBase kp) w :=
  h.frame A n v (fun a ia => ctx.stackWindow a (inStack a ia))

theorem Carried.slot10Mapped {w : Window} {d : MachineData}
    (h : Carried layout preempt kp s0 w d) :
    ∃ x, d.dmem.loadInt (s0.data.regs.rsp.toBitVec + 16#64) 8 = some x := by
  apply Option.isSome_iff_exists.mp
  rw [loadInt_defined]
  intro i hi
  exact h.stack _ (slot10_stack ⟨i, hi, rfl⟩)

theorem Carried.slot18Mapped {w : Window} {d : MachineData}
    (h : Carried layout preempt kp s0 w d) :
    ∃ x, d.dmem.loadInt (s0.data.regs.rsp.toBitVec + 24#64) 8 = some x := by
  apply Option.isSome_iff_exists.mp
  rw [loadInt_defined]
  intro i hi
  exact h.stack _ (slot18_stack ⟨i, hi, rfl⟩)

end

#print axioms region_step
#print axioms call_step
#print axioms Carried.store
end Binary.C2
