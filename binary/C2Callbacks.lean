import C2CutInterfaces
import CallbackCmp8

/-! Work package 1 of result C2, the C2 side: `StubsAgree`, `BtsSupported`,
`RegionsLaidOut` and the three call-site rules (`PcSite`, `Cmp8Site`, `ConstCmp8Site`)
of `C2CutInterfaces`. The package owns this file. All of its proofs are here: a further flat module is
not buildable without a lakefile entry, and one in a subdirectory would be outside the
source scan of `scripts/binary-proof-gate`.

| Proposition | Theorem |
| --- | --- |
| `StubsAgree` | `stubs_agree` |
| `PcSite`, `Cmp8Site`, `ConstCmp8Site` | `pc_site`, `cmp8_site`, `const_cmp8_site` (closed: no hypothesis) |
| `BtsSupported` | `bts_supported` |
| `RegionsLaidOut` | `regions_laid_out` | -/

/-! ## The call-site rule from a callback rule

`call_site` proves `CallSite callee` from a rule `Leaf fetch callee plan` for a plan
whose stores have the coverage shape (`Callback.Cmp8.Covered`). The call pushes the
return address into the range's own stack bytes; the callback's readiness comes from
`Carried.coverage` and the separations of `Context`, which are needed, and hold, only
in a recording mode; the callback's exact stores re-establish the coverage state and
lie inside the coverage buffer; and every state inside the callback is in the
callbacks' text, which holds no exit of the range. -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-! ## Memory facts -/

theorem storeInt_get_mapped (m : Mem 64) (a b : BitVec 64) (k : Nat) (v : Int)
    (mapped : (m.get? a).isSome = true) : ((m.storeInt b k v).get? a).isSome = true := by
  simp only [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union] at mapped ⊢
  cases stored : ((Int.toBytes k v).At b)[a]? with
  | some x => rfl
  | none => exact mapped

theorem equalOutside_weaken {p q : BitVec 64 → Prop} {a b : Mem 64}
    (equal : EqualOutside p a b) (implies : ∀ x, p x → q x) : EqualOutside q a b :=
  fun x outside => equal x (fun inside => outside (implies x inside))

/-- The window is read from the window bytes only. -/
theorem WindowAt.ofEqualOutside {writes : BitVec 64 → Prop} {m m' : Mem 64} {kp : BitVec 64} {w : Window}
    (equal : EqualOutside writes m m')
    (apart : ∀ a, windowBytes kp a → ¬writes a)
    (window : WindowAt m (windowBase kp) w) : WindowAt m' (windowBase kp) w := by
  obtain ⟨counter, words⟩ := window
  constructor
  · rw [← equal.loadInt _ 8 ?_]
    · exact counter
    · intro byte bound
      apply apart
      refine ⟨Layouts.replay_counter + byte, ?_, ?_⟩
      · simp only [Layouts.replay_counter, Layouts.replaySize]
        omega
      · simp only [BitVec.ofNat_add, BitVec.add_assoc]
  · intro i bound
    rw [← equal.loadInt _ _ ?_]
    · exact words i bound
    · intro byte byteBound
      apply apart
      refine ⟨Layouts.replay_backtrack + i * Layouts.replayWordBytes + byte, ?_, ?_⟩
      · simp only [Layouts.replay_backtrack, Layouts.replayWordBytes, Layouts.replaySize,
          Layouts.replayWords] at bound byteBound ⊢
        omega
      · simp only [BitVec.ofNat_add, BitVec.add_assoc]

/-- A byte of the two spill slots is a stack byte of the range and is not in the
return-address slot of its calls. -/
theorem spill_byte (sp a : BitVec 64) (k : Nat) (bound : k < 16)
    (at_ : a = sp + 0x10 + .ofNat 64 k) :
    stackBytes sp a ∧ ¬InRange (sp - 8) 8 a := by
  subst at_
  refine ⟨.inr ⟨k, bound, rfl⟩, ?_⟩
  have moved : sp + 0x10 + BitVec.ofNat 64 k = (sp - 8) + .ofNat 64 24 + .ofNat 64 k := by
    congr 1
    bv_omega
  have based : InRange (sp - 8) 8 = InRange ((sp - 8) + .ofNat 64 0) 8 := by simp
  rw [moved, based]
  exact InRange.offset_disjoint (sp - 8) 24 16 0 8 (by decide) (by decide) (.inr (by decide)) _
    ⟨k, bound, rfl⟩

/-- No exit of the range is in the callbacks' text. -/
theorem text_not_exit (p : Int64) (text : Callback.Cmp8.Text p) : p ∉ exits := by
  intro member
  have none1 : ServiceImage.fetch Range.donePC = none := by rfl
  have none2 : ServiceImage.fetch Range.rejectWindowPC = none := by rfl
  have none3 : ServiceImage.fetch Range.rejectLimitPC = none := by rfl
  have none4 : Callback.Cmp8.fetch Range.donePC = none := by rfl
  have none5 : Callback.Cmp8.fetch Range.rejectWindowPC = none := by rfl
  have none6 : Callback.Cmp8.fetch Range.rejectLimitPC = none := by rfl
  simp only [exits, List.mem_cons, List.not_mem_nil, or_false] at member
  unfold Callback.Cmp8.Text at text
  rcases member with rfl | rfl | rfl
  · rw [none1, none4] at text
    simp at text
  · rw [none2, none5] at text
    simp at text
  · rw [none3, none6] at text
    simp at text

/-! ## The call site -/

/-- THE CALL SITE, from a rule. A callee with a rule for a plan of the coverage shape
meets `CallSite`. -/
theorem call_site {callee : Int64} {plan : MachineState → Option (List WordWrite)}
    (covered : Callback.Cmp8.Covered plan)
    (leaf : ∀ fetch, Reading fetch → Callback.Cmp8.Leaf fetch callee plan) :
    CallSite callee := by
  intro fetch layout preempt s0 kp skb nonce w d pc target history reading context here
    targetEq notExit carried
  have sp : d.regs.rsp = s0.data.regs.rsp := carried.rsp
  have pushIn : ∀ a, InRange (d.regs.rsp.toBitVec - 8) 8 a →
      stackBytes s0.data.regs.rsp.toBitVec a := by
    intro a inside
    rw [sp] at inside
    exact .inl inside
  have mapped : (d.dmem.loadInt (d.regs.rsp.toBitVec - 8) 8).isSome = true := by
    rw [loadInt_defined]
    intro i bound
    exact carried.stack _ (pushIn _ ⟨i, bound, rfl⟩)
  have call := historySteps_eventually fetch 1 _ _
    (Instrumentation.call_instruction fetch pc target here d history mapped)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro entered ⟨machine, recorded⟩
  have cursor : entered = ⟨Instrumentation.calledState d (pc + 5) (label target),
      history ++ [Instrumentation.calledState d (pc + 5) (label target)]⟩ := by
    cases entered; simp_all
  rw [cursor]
  have entry := Instrumentation.called_entry d (pc + 5) (label target)
    (by rw [sp]; exact context.aligned)
  have pushed : EqualOutside (InRange (d.regs.rsp.toBitVec - 8) 8) d.dmem
      (Instrumentation.calledState d (pc + 5) (label target)).data.dmem :=
    storeInt_frame d.dmem (d.regs.rsp.toBitVec - 8) 8 (pc + 5).toBitVec.toInt
  have state : KcovState layout (preempt + 0x200)
      (Instrumentation.calledState d (pc + 5) (label target)).data.dmem :=
    Kcov.state_frame layout _ _ _ carried.coverage _ pushed (by
      intro a bytes inPush
      have inStack := pushIn a inPush
      rcases bytes with metadata | count | storage
      · exact context.coverageApart a (.inl metadata) (.inl inStack)
      · exact context.stackPreempt a inStack count
      · exact context.coverageApart a (.inr storage) (.inl inStack))
  have service := Callback.Cmp8.Leaf.callback (leaf fetch reading) covered layout (preempt + 0x200)
    (Instrumentation.calledState d (pc + 5) (label target)) (pc + 5).toUInt64 targetEq entry state
    (fun active a inBuffer inSlot =>
      context.coverageApart a (.inr ⟨active, .inr inBuffer⟩) (.inl (pushIn a inSlot)))
    (fun active a inBuffer metadata => context.coverageMetadata a active (.inr inBuffer) metadata)
    (fun active a inBuffer count =>
      context.coverageApart a (.inr ⟨active, .inr inBuffer⟩) (.inr (.inr count)))
  have joined := history_prepend fetch _ _ (history_last fetch _ _ rfl service) history
  apply eventually_weaken (historyStep fetch) _ _ _ _ joined
  rintro e ⟨inner, ⟨⟨returned, kept, frame, interior⟩, last⟩, machine, recordedE⟩
  obtain ⟨atPc, rsp, rbx, rbp, r12, r13, r14, r15⟩ :=
    Instrumentation.returned_caller d (pc + 5) (label target) inner.machine returned
  rw [machine]
  have whole := pushed.trans frame
  have stackApart : ∀ a, stackBytes s0.data.regs.rsp.toBitVec a →
      ¬((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovBufferBytes layout a) :=
    fun a inStack inBuffer =>
      context.coverageApart a (.inr ⟨inBuffer.1, .inr inBuffer.2⟩) (.inl inStack)
  have spill : ∀ k, k < 16 → ¬(InRange (d.regs.rsp.toBitVec - 8) 8
        (s0.data.regs.rsp.toBitVec + 0x10 + .ofNat 64 k) ∨
      ((layout.mode = 2 ∨ layout.mode = 3) ∧
        KcovBufferBytes layout (s0.data.regs.rsp.toBitVec + 0x10 + .ofNat 64 k))) := by
    intro k bound
    have byte := spill_byte s0.data.regs.rsp.toBitVec _ k bound rfl
    rw [sp]
    rintro (inPush | inBuffer)
    · exact byte.2 inPush
    · exact stackApart _ byte.1 inBuffer
  refine ⟨atPc, ?_, rbp, r14, r15, ?_, ?_, ?_⟩
  · exact {
      coverage := kept
      window := WindowAt.ofEqualOutside whole (by
        rintro a inWindow (inPush | inBuffer)
        · exact context.stackWindow a (pushIn a inPush) inWindow
        · exact context.coverageApart a (.inr ⟨inBuffer.1, .inr inBuffer.2⟩)
            (.inr (.inl inWindow))) carried.window
      stack := by
        intro a inStack
        rw [← frame a (stackApart a inStack)]
        exact storeInt_get_mapped _ _ _ _ _ (carried.stack a inStack)
      frame := equalOutside_weaken (carried.frame.trans whole) (by
        rintro a (old | inPush | inBuffer)
        · exact old
        · exact .inl (.inl (pushIn a inPush))
        · exact .inr ⟨inBuffer.1, .inr inBuffer.2⟩)
      rsp := rsp.trans sp
      rbx := rbx.trans carried.rbx
      r12 := r12.trans carried.r12
      r13 := r13.trans carried.r13 }
  · exact (whole.loadInt _ 8 (fun i bound => spill i (by omega))).symm
  · refine (whole.loadInt _ 8 (fun i bound => ?_)).symm
    have moved : s0.data.regs.rsp.toBitVec + 0x18 + BitVec.ofNat 64 i =
        s0.data.regs.rsp.toBitVec + 0x10 + BitVec.ofNat 64 (8 + i) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      congr 1
      bv_omega
    rw [moved]
    exact spill (8 + i) (by omega)
  · intro quiet u member
    rw [recordedE] at member
    rcases List.mem_append.mp member with before | inside
    · exact quiet u before
    · rw [← history_restore last] at inside
      rcases List.mem_append.mp inside with interiorState | final
      · exact text_not_exit u.pc (interior u interiorState).2
      · rw [List.mem_singleton.mp final, atPc]
        exact notExit

/-! ## The adapter -/

/-- The addresses at which a literal code list has an instruction. -/
def starts (pc : Int64) : List (Kraken.Sized Directive) → List Int64
  | [] => []
  | ⟨_, n⟩ :: rest => pc :: starts (pc + .ofNat n) rest

theorem fetchIn_start {pc : Int64} {code : List (Kraken.Sized Directive)} {target : Int64}
    {instruction : Decoded} (read : Image.fetchIn pc code target = some instruction) :
    target ∈ starts pc code := by
  induction code generalizing pc with
  | nil => simp [Image.fetchIn] at read
  | cons head rest ih =>
    obtain ⟨d, n⟩ := head
    unfold Image.fetchIn at read
    split at read
    · rename_i equal
      rw [equal]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih read)

theorem stubs_agree : StubsAgree := by
  intro fetch agree
  constructor
  · intro pc instruction read
    apply agree
    have member := fetchIn_start read
    have list : starts Callback.Cmp8.cmp8Entry Callback.Cmp8.cmp8Stub =
        (Callback.Cmp8.addresses.take 5) := by rfl
    rw [list] at member
    simp only [Callback.Cmp8.addresses, List.take_succ_cons, List.take_zero, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact (by rfl : Range.fetch _ = _).trans read
  · intro pc instruction read
    apply agree
    have member := fetchIn_start read
    have list : starts Callback.Cmp8.constCmp8Entry Callback.Cmp8.constCmp8Stub =
        (Callback.Cmp8.addresses.drop 5) := by rfl
    rw [list] at member
    simp only [Callback.Cmp8.addresses, List.drop_succ_cons, List.drop_zero, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact (by rfl : Range.fetch _ = _).trans read

/-! ## The call sites, closed -/

theorem pc_site : PcSite :=
  call_site (Callback.Cmp8.kcov_covered .pc)
    (fun fetch reading => Callback.Cmp8.pc_rule fetch reading.services)

theorem cmp8_site : Cmp8Site :=
  call_site (Callback.Cmp8.record_covered 6)
    (fun fetch reading =>
      Callback.Cmp8.cmp8_rule fetch reading.services (stubs_agree fetch reading.range).1)

theorem const_cmp8_site : ConstCmp8Site :=
  call_site (Callback.Cmp8.record_covered 7)
    (fun fetch reading =>
      Callback.Cmp8.const_cmp8_rule fetch reading.services (stubs_agree fetch reading.range).2)

/-! ## `bts` and the layout -/

theorem bts_supported : BtsSupported := by
  intro dst index s p n₁ n₂ j₁ j₂ P Q hn hj
  change (@Operation.interp _ ⟨.W64⟩ .W64 (.bts dst index) p s n₁ j₁).All P →
    (@Operation.interp _ ⟨.W64⟩ .W64 (.bts dst index) p s n₂ j₂).All Q
  simp only [Operation.interp]
  split
  · exact False.elim
  · split
    · exact False.elim
    · simp only [Effects.All]
      split
      · exact False.elim
      · intro run pf af zf sf of
        exact hn _ (run pf af zf sf of)

/-- A literal code list of instructions, each of positive length and monotone in its
continuations. -/
inductive Supported : List (Kraken.Sized Directive) → Prop
  | nil : Supported []
  | cons (i : Instr) (n : Nat) (tail : List (Kraken.Sized Directive))
      (positive : 0 < n) (mono : CpsMono i) (rest : Supported tail) :
      Supported (⟨.instr i, n⟩ :: tail)

theorem start_offset {pc : Int64} {code : List (Kraken.Sized Directive)} {target : Int64}
    (supported : Supported code) (member : target ∈ starts pc code) :
    ∃ k, k < (code.map (·.size)).sum ∧ target = pc + .ofNat k := by
  induction supported generalizing pc with
  | nil => simp [starts] at member
  | cons i n tail positive mono rest ih =>
    simp only [starts, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨0, by simp only [List.map_cons, List.sum_cons]; omega, by simp⟩
    · obtain ⟨k, bound, at_⟩ := ih member
      refine ⟨n + k, by simp only [List.map_cons, List.sum_cons]; omega, ?_⟩
      rw [at_, Int64.ofNat_add, Int64.add_assoc]

theorem offset_ne (pc : Int64) (m : Nat) (positive : 0 < m) (bound : m < 2 ^ 64) :
    pc + .ofNat m ≠ pc := by
  intro equal
  have bits := congrArg Int64.toBitVec equal
  rw [Int64.toBitVec_add] at bits
  have zero : (Int64.ofNat m).toBitVec = 0 := by
    have := congrArg (fun x => x - pc.toBitVec) bits
    simpa [BitVec.add_comm pc.toBitVec, BitVec.add_sub_cancel] using this
  have nat := congrArg BitVec.toNat zero
  simp at nat
  omega

/-- A supported code list that does not wrap the address space is laid out under its
own literal fetch: no later instruction starts at an earlier one's address. -/
theorem fetchIn_laid_out {code : List (Kraken.Sized Directive)} (supported : Supported code)
    (pc : Int64) (bound : (code.map (·.size)).sum < 2 ^ 64) :
    LaidOut (Image.fetchIn pc code) pc code := by
  induction supported generalizing pc with
  | nil => exact .nil _
  | cons i n tail positive mono rest ih =>
    simp only [List.map_cons, List.sum_cons] at bound
    refine .cons pc i n tail positive (by simp [Image.fetchIn]) mono ?_
    apply (ih (pc + .ofNat n) (by omega)).agreement
    intro p instruction read
    unfold Image.fetchIn
    split
    · rename_i equal
      obtain ⟨k, small, at_⟩ := start_offset rest (fetchIn_start read)
      rw [equal, Int64.add_assoc, ← Int64.ofNat_add] at at_
      exact absurd at_.symm (offset_ne pc (n + k) (by omega) (by omega))
    · exact read

/-- Every instruction of the range is supported: by the landed lemma, or for the `bts`
by `bts_supported`. -/
theorem range_supported : Supported Range.code := by
  repeat' first
    | exact Supported.nil
    | refine Supported.cons _ _ _ (by decide)
        (by first
          | exact regular_mono _ _ _ True.intro
          | exact bts_supported _ _) ?_

/-- The whole range is laid out at its entry under its own literal fetch. -/
theorem range_laid_out : LaidOut Range.fetch Range.entry Range.code := by
  apply (fetchIn_laid_out range_supported Range.entry (by decide +kernel)).agreement
  intro p instruction read
  simp [Range.fetch, read]

theorem laidOut_take {fetch : Int64 → Option Decoded} {pc : Int64}
    {code : List (Kraken.Sized Directive)} (layout : LaidOut fetch pc code) (n : Nat) :
    LaidOut fetch pc (code.take n) := by
  induction layout generalizing n with
  | nil => simp only [List.take_nil]; exact .nil _
  | cons pc i len tail positive here mono rest ih =>
    cases n with
    | zero => exact .nil _
    | succ n => exact .cons pc i len _ positive here mono (ih n)

theorem laidOut_drop {fetch : Int64 → Option Decoded} {pc : Int64}
    {code : List (Kraken.Sized Directive)} (layout : LaidOut fetch pc code) (n : Nat) :
    LaidOut fetch (pc + .ofNat ((code.take n).map (·.size)).sum) (code.drop n) := by
  induction layout generalizing n with
  | nil pc => simp only [List.drop_nil]; exact .nil _
  | cons pc i len tail positive here mono rest ih =>
    cases n with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, List.drop_zero]
      have same : pc + Int64.ofNat 0 = pc := by simp
      rw [same]
      exact .cons pc i len tail positive here mono rest
    | succ n =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.drop_succ_cons]
      have moved : pc + Int64.ofNat (len + ((tail.take n).map (·.size)).sum) =
          pc + Int64.ofNat len + Int64.ofNat ((tail.take n).map (·.size)).sum := by
        rw [Int64.ofNat_add, Int64.add_assoc]
      rw [moved]
      exact ih n

theorem regions_laid_out : RegionsLaidOut := by
  intro fetch agree first count _
  exact laidOut_take (laidOut_drop (range_laid_out.agreement agree) first) count

#print axioms call_site
#print axioms stubs_agree
#print axioms pc_site
#print axioms cmp8_site
#print axioms const_cmp8_site
#print axioms bts_supported
#print axioms regions_laid_out
end Binary.C2
