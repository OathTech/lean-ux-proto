import CallbackCmp8Rule
import KcovInvariant
import CallbackWrappers
import CallbackPc
import CallbackLeafHistory

/-! Proofs of the callback rules of `CallbackCmp8Rule` (`PcRule`, `Cmp8Rule`,
`ConstCmp8Rule`) from the image. Work package 1 of result C2 owns this file and every
file named `CallbackCmp8*` other than `CallbackCmp8Image` and `CallbackCmp8Rule`, which
are frozen. Neutral: nothing here may import a `C2*` or a `StatementC1*` module, so
that the C1 branch can take the proofs unchanged. New files are imported from here; the
lakefile is not edited. Brief: packets/c2/proof/WP1.md. -/

/-! ## Coverage readiness

Coverage readiness for a callback whose stores are given by any plan, the constant
8-byte form (tag 7, no `KcovKind`) included.

The landed `Kcov` lemmas are stated by `KcovKind`. What a caller needs of a plan is only
the shape of its stores (`Shaped`): none, or the incremented count word followed by
stores to later words of the buffer. That shape gives readiness and re-establishes
`KcovState`, and the separations are needed only when there are stores, which happens
only in a recording mode. `KcovPlan kind` has the shape by the landed normal form;
`recordPlan tag` has it because it is `recordPlan 6`, which is `KcovPlan .cmp8`, with
the value of one store changed (`recordPlan_retag`).
-/
namespace Binary.Callback.Cmp8
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Replace the value of the second store (the record's tag). -/
def retag (tag : BitVec 64) : List WordWrite → List WordWrite
  | first :: second :: rest => first :: ⟨second.address, tag⟩ :: rest
  | other => other

theorem bind_map_congr {α β γ : Type} (x : Option α) (f' : α → Option γ) (f : α → Option β)
    (g : β → γ) (pointwise : ∀ a, f' a = (f a).map g) :
    x >>= f' = (x >>= f).map g := by
  cases x with
  | none => rfl
  | some a => exact pointwise a

/-- The 8-byte plans differ in the tag's value only. -/
theorem recordPlan_retag (tag : BitVec 64) (s : MachineState) :
    recordPlan tag s = (recordPlan 6 s).map (retag tag) := by
  unfold recordPlan
  repeat' first
    | rfl
    | refine bind_map_congr _ _ _ _ (fun _ => ?_)
    | split
    | dsimp only

/-- The stores of a coverage callback: none, or (in a recording mode) the incremented
count word and then stores to later words inside the buffer. -/
def Shaped (layout : KcovLayout) (stores : List WordWrite) : Prop :=
  stores = [] ∨ ((layout.mode = 2 ∨ layout.mode = 3) ∧ ∃ count tail,
    stores = ⟨layout.area, .ofNat 64 (count + 1)⟩ :: tail ∧
    count + 1 ≤ layout.capacity.toNat ∧
    ∀ write ∈ tail, ∃ word, 0 < word ∧ word < layout.capacity.toNat ∧
      write.address = layout.area + .ofNat 64 (8 * word))

/-- A plan whose stores have the coverage shape in every valid coverage state. -/
def Covered (plan : MachineState → Option (List WordWrite)) : Prop :=
  ∀ (layout : KcovLayout) (preempt : BitVec 32) (s : MachineState) (returnPC : BitVec 64),
    KcovState layout preempt s.data.dmem →
    load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC →
    ∃ stores, plan s = some stores ∧ Shaped layout stores

theorem kcov_covered (kind : KcovKind) : Covered (KcovPlan kind) := by
  intro layout preempt s returnPC state returnRead
  by_cases active : layout.mode = 2 ∨ layout.mode = 3
  · obtain ⟨count, countBound, countRead⟩ := (state.2.2 active).2
    have normal := Kcov.plan_normal_form kind layout s preempt returnPC count state.1
      state.2.1 returnRead countRead countBound
    refine ⟨_, normal, ?_⟩
    split
    · rcases Kcov.bufferPlan_shape kind layout count returnPC (Kcov.argument kind s .rdi)
        (Kcov.argument kind s .rsi) with empty | ⟨tail, shape, bound, payload⟩
      · exact .inl empty
      · exact .inr ⟨active, count, tail, shape, bound, payload⟩
    · exact .inl rfl
  · refine ⟨[], ?_, .inl rfl⟩
    apply Kcov.inactive_plan kind layout s preempt returnPC state.1 state.2.1 returnRead
    split <;> intro mode <;> exact active (by simp_all)

theorem retag_shaped (tag : BitVec 64) (layout : KcovLayout) (stores : List WordWrite)
    (shaped : Shaped layout stores) : Shaped layout (retag tag stores) := by
  rcases shaped with empty | ⟨active, count, tail, shape, bound, payload⟩
  · subst empty
    exact .inl rfl
  · subst shape
    cases tail with
    | nil => exact .inr ⟨active, count, [], rfl, bound, payload⟩
    | cons second rest =>
      refine .inr ⟨active, count, ⟨second.address, tag⟩ :: rest, rfl, bound, ?_⟩
      intro write member
      rcases List.mem_cons.mp member with rfl | member
      · exact payload second (by simp)
      · exact payload write (by simp [member])

theorem record_covered (tag : BitVec 64) : Covered (recordPlan tag) := by
  intro layout preempt s returnPC state returnRead
  obtain ⟨stores, plan, shaped⟩ := kcov_covered .cmp8 layout preempt s returnPC state returnRead
  refine ⟨retag tag stores, ?_, retag_shaped tag layout stores shaped⟩
  rw [recordPlan_retag, recordPlan_cmp8, plan]
  rfl

/-- Every store of a shaped plan is to a word of the buffer. -/
theorem shaped_addresses {layout : KcovLayout} {stores : List WordWrite}
    (shaped : Shaped layout stores) (write : WordWrite) (member : write ∈ stores) :
    (layout.mode = 2 ∨ layout.mode = 3) ∧ ∃ word < layout.capacity.toNat,
      write.address = layout.area + .ofNat 64 (8 * word) := by
  rcases shaped with empty | ⟨active, count, tail, shape, bound, payload⟩
  · simp [empty] at member
  · rw [shape] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨active, 0, by omega, by simp⟩
    · obtain ⟨word, _, wordBound, address⟩ := payload write member
      exact ⟨active, word, wordBound, address⟩

/-- Readiness from the coverage state; the return slot has to be apart from the buffer
only in a recording mode. -/
theorem ready_of_covered {plan : MachineState → Option (List WordWrite)} (covered : Covered plan)
    (layout : KcovLayout) (preempt : BitVec 32) (s : MachineState) (returnPC : BitVec 64)
    (state : KcovState layout preempt s.data.dmem)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (stack : layout.mode = 2 ∨ layout.mode = 3 →
      KcovSeparated layout (InRange s.data.regs.rsp.toBitVec 8)) :
    Ready plan s := by
  obtain ⟨stores, computed, shaped⟩ := covered layout preempt s returnPC state returnRead
  refine ⟨stores, computed, ?_⟩
  intro write member
  obtain ⟨active, word, bound, atWord⟩ := shaped_addresses shaped write member
  constructor
  · rw [atWord]
    exact (state.2.2 active).1 word bound
  · intro address inside
    rw [atWord] at inside
    exact stack active address (Kcov.word_in_buffer layout word bound address inside)

/-- Shaped stores keep the buffer invariant: the count word read back is the
incremented count, and no later store touches it. -/
theorem shaped_preserves {layout : KcovLayout} {stores : List WordWrite}
    (shaped : Shaped layout stores) (memory : Mem 64) (buffer : KcovBuffer layout memory) :
    KcovBuffer layout (Kcov.storesMemory stores memory) := by
  obtain ⟨mapped, old⟩ := buffer
  constructor
  · intro word bound
    exact Kcov.stores_mapped _ _ _ _ (mapped word bound)
  · rcases shaped with empty | ⟨_, count, tail, shape, bound, payload⟩
    · rw [empty]
      exact old
    · rw [shape]
      refine ⟨count + 1, bound, ?_⟩
      have frame := Kcov.stores_frame tail
        (memory.storeInt layout.area 8 (BitVec.ofNat 64 (count + 1)).toInt)
        (fun address => ¬InRange layout.area 8 address) (by
          intro write member address inside
          obtain ⟨word, positive, wordBound, addressEq⟩ := payload write member
          rw [addressEq] at inside
          have disjoint := Kcov.word_disjoint layout.area word 0
            (Nat.lt_trans wordBound layout.capacity.isLt) (by decide) (by omega) address inside
          simpa using disjoint)
      have readback := load64_store memory layout.area (.ofNat 64 (count + 1))
      have tailRead := frame.loadInt layout.area 8 (by
        intro byte bound
        intro outside
        exact outside ⟨byte, bound, rfl⟩)
      change load64 (Kcov.storesMemory tail (memory.storeInt layout.area 8
        (BitVec.ofNat 64 (count + 1)).toInt)) layout.area = _
      unfold load64
      rw [← tailRead, readback]
      simp only [Option.map_some, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The exact stores of a covered plan re-establish the coverage state and change
nothing outside the buffer, and nothing at all outside a recording mode. The
separations of the buffer from the metadata and the preempt count are needed only in a
recording mode. -/
theorem preserved_of_covered {plan : MachineState → Option (List WordWrite)}
    (covered : Covered plan)
    (layout : KcovLayout) (preempt : BitVec 32) (s t : MachineState) (returnPC : BitVec 64)
    (state : KcovState layout preempt s.data.dmem)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (metadataSeparate : layout.mode = 2 ∨ layout.mode = 3 →
      KcovSeparated layout (KcovMetadataBytes layout))
    (preemptSeparate : layout.mode = 2 ∨ layout.mode = 3 →
      KcovSeparated layout (InRange preemptCountAddress 4))
    (effect : Effect plan s t) :
    KcovState layout preempt t.data.dmem ∧
      EqualOutside (fun a => (layout.mode = 2 ∨ layout.mode = 3) ∧ KcovBufferBytes layout a)
        s.data.dmem t.data.dmem := by
  obtain ⟨stores, computed, shaped⟩ := covered layout preempt s returnPC state returnRead
  obtain ⟨stores', computed', after⟩ := effect
  rw [computed] at computed'
  cases Option.some.inj computed'
  change t.data.dmem = Kcov.storesMemory stores s.data.dmem at after
  have frame : EqualOutside
      (fun a => (layout.mode = 2 ∨ layout.mode = 3) ∧ KcovBufferBytes layout a)
      s.data.dmem t.data.dmem := by
    rw [after]
    apply Kcov.stores_frame
    intro write member address inside
    obtain ⟨active, word, bound, atWord⟩ := shaped_addresses shaped write member
    rw [atWord] at inside
    exact ⟨active, Kcov.word_in_buffer layout word bound address inside⟩
  refine ⟨?_, frame⟩
  by_cases active : layout.mode = 2 ∨ layout.mode = 3
  · have bufferFrame : EqualOutside (KcovBufferBytes layout) s.data.dmem t.data.dmem :=
      fun address outside => frame address (fun inside => outside inside.2)
    refine ⟨Kcov.metadata_frame layout _ _ state.1 bufferFrame (metadataSeparate active), ?_, ?_⟩
    · have read := bufferFrame.loadInt preemptCountAddress 4 (by
        intro byte bound written
        exact preemptSeparate active _ written ⟨byte, bound, rfl⟩)
      simpa only [load32, ← read] using state.2.1
    · intro _
      rw [after]
      exact shaped_preserves shaped s.data.dmem (state.2.2 active)
  · have same : t.data.dmem = s.data.dmem := by
      rcases shaped with empty | ⟨recording, _⟩
      · rw [after, empty]
        rfl
      · exact absurd recording active
    rw [same]
    exact state

/-- A rule applied from the coverage state: the callback returns, the coverage state
is kept, memory is changed only inside the buffer and only in a recording mode, and the
interior is in the callbacks' text. The counterpart of the landed `Kcov.callback` for a
plan of any tag, with the separations asked for only in a recording mode. -/
theorem Leaf.callback {fetch : Int64 → Option Decoded} {address : Int64}
    {plan : MachineState → Option (List WordWrite)} (leaf : Leaf fetch address plan)
    (covered : Covered plan)
    (layout : KcovLayout) (preempt : BitVec 32) (s : MachineState) (returnAddress : UInt64)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : KcovState layout preempt s.data.dmem)
    (stack : layout.mode = 2 ∨ layout.mode = 3 →
      KcovSeparated layout (InRange s.data.regs.rsp.toBitVec 8))
    (metadata : layout.mode = 2 ∨ layout.mode = 3 →
      KcovSeparated layout (KcovMetadataBytes layout))
    (preemptFrame : layout.mode = 2 ∨ layout.mode = 3 →
      KcovSeparated layout (InRange preemptCountAddress 4)) :
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        KcovState layout preempt t.machine.data.dmem ∧
        EqualOutside (fun a => (layout.mode = 2 ∨ layout.mode = 3) ∧ KcovBufferBytes layout a)
          s.data.dmem t.machine.data.dmem ∧
        ∀ q ∈ t.history.dropLast, Interior s.data.regs.rsp q) ⟨s, [s]⟩ := by
  have returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnAddress.toBitVec := by
    simp only [load64, entry.2, Option.map_some, BitVec.ofInt_natCast]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    simp
  have run := leaf s returnAddress atEntry
    (ready_of_covered covered layout preempt s returnAddress.toBitVec state returnRead stack) entry
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨returned, _, effect, interior⟩
  have preserved := preserved_of_covered covered layout preempt s t.machine
    returnAddress.toBitVec state returnRead metadata preemptFrame effect
  exact ⟨returned, preserved.1, preserved.2, interior⟩

#print axioms recordPlan_retag
#print axioms kcov_covered
#print axioms record_covered
#print axioms ready_of_covered
#print axioms preserved_of_covered
#print axioms Leaf.callback

/-! ## The interior -/

/-- Every guarded step fetched its instruction, so its program counter is in the
domain of the fetch it ran under. -/
theorem guarded_fetched {fetch : Int64 → Option Decoded} {guard P : MachineState → Prop}
    {s : MachineState} (run : Eventually (guardedStep fetch guard) P s) :
    Eventually (guardedStep fetch (fun q => guard q ∧ (fetch q.pc).isSome = true)) P s := by
  induction run with
  | done s hp => exact .done s hp
  | step s mid step _ ih =>
    apply step_cps
    refine ⟨⟨step.1, ?_⟩, instruction_mono fetch s _ _ ih step.2⟩
    have fetched := step.2
    unfold instructionStep at fetched
    cases read : fetch s.pc with
    | none => simp [read] at fetched
    | some _ => rfl

/-- A run of the shared service bodies, under the ambient decoder, with its interior
in the callbacks' text. -/
theorem service_interior {fetch : Int64 → Option Decoded} (services : ServiceDecoderAgreement fetch)
    {rsp : UInt64} {P : MachineState → Prop} {s : MachineState}
    (run : Eventually (guardedStep ServiceImage.fetch (leafGuard rsp)) P s) :
    Eventually (guardedStep fetch (Interior rsp)) P s := by
  apply guarded_agreement services
  apply change_guard _ (guarded_fetched run)
  intro t guarded
  exact ⟨guarded.1, .inl guarded.2⟩

/-- A guarded run recorded as a history gives the rule's conclusion. -/
theorem leaf_of_run {fetch : Int64 → Option Decoded} {address : Int64}
    {plan : MachineState → Option (List WordWrite)}
    (run : ∀ s ra, s.pc = address → Ready plan s → EntryFrame s ra →
      Eventually (guardedStep fetch (Interior s.data.regs.rsp))
        (fun t => Returned s t ra ∧ EqualOutside (Writes plan s) s.data.dmem t.data.dmem ∧
          Effect plan s t) s) :
    Leaf fetch address plan := by
  intro s ra pc ready frame
  have history := guarded_history fetch _ _ s (run s ra pc ready frame) [] (by simp)
  apply eventually_weaken (historyStep fetch) _ _ _ _ history
  rintro t ⟨⟨returned, framed, effect⟩, interior⟩
  exact ⟨returned, framed, effect, interior⟩

/-- `PcRule`: the landed `pc_run`, its interior confined to the callbacks' text. -/
theorem pc_rule : PcRule := by
  intro fetch services
  apply leaf_of_run
  rintro ⟨s, p⟩ ra pc ready frame
  change p = _ at pc
  subst p
  exact service_interior services (pc_run s ra ready frame)

#print axioms pc_rule
end Binary.Callback.Cmp8
