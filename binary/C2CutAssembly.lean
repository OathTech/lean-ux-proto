import C2CutInterfaces

/-! Result C2, the cut of the proof: the assembly.

The headline's clauses that need only the mirror (`ExitsCleanly`, `Refines`,
`ReplayWitness`) proved from the interface propositions of `C2CutInterfaces` as
hypotheses. The fourth clause, `NoCounterAcceptedTwice`, needs the proof tree's
`CounterWindow` theorems and is assembled in the bridge library (`bridge/C2Bridge`),
from `Refines` and the propositions bundled in `Representation` here.

These theorems are conditional: each hypothesis is a proposition a work package still
has to prove. Nothing here is a result about the image until they are discharged. -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-! ## Derived propositions -/

/-- The whole advance path, +161 to +280. -/
def AdvanceSegment : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64) (w : Window) (t : BitVec 64) (e : Executed),
    Reading fetch → Context layout preempt s kp skb nonce →
    AtAdvance layout preempt kp s w t e →
    Eventually (historyStep fetch) (AtTail layout preempt kp s (advance w t) t) e

/-- The range against the pivot: from every entry state whose window bytes hold `w`,
the machine reaches, as its first exit, the outcome `validate w nonce`, with the carried
invariant for the outcome's window. -/
def RangeSimulates : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64) (w : Window),
    Reading fetch → Context layout preempt s kp skb nonce →
    WindowAt s.data.dmem (windowBase kp) w →
    Eventually (historyStep fetch) (AtExit layout preempt kp s (validate w nonce)) ⟨s, [s]⟩

/-- `Refines` with one more conjunct at the exit: the stack slots are still mapped.
The witness needs it to enter the range a second time. -/
def StrongRefines : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64)
    (world world' : WGWorld) (ambient ambient' : Ambient) (id : WG.KeypairId)
    (c : WG.ReplayCounter) (result : Bool),
    Reading fetch → Context layout preempt s kp skb nonce →
    Layouts.ReplayFields s.data.dmem (windowBase kp) c →
    windowOf world id = some c →
    ((WG.counterValidate id nonce.toNat).run world).run ambient = .ok ((result, world'), ambient') →
    Eventually (historyStep fetch)
      (fun e => e.machine.pc = exitPC c nonce.toNat ∧
        (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧
        accepted e.machine = result ∧
        (∃ c', windowOf world' id = some c' ∧
          Layouts.ReplayFields e.machine.data.dmem (windowBase kp) c') ∧
        Kept layout preempt kp s e.machine ∧
        (∀ a, stackBytes s.data.regs.rsp.toBitVec a → (e.machine.data.dmem.get? a).isSome = true))
      ⟨s, [s]⟩

/-- What work package 2 delivers. -/
structure Execution : Prop where
  head : HeadSegment
  enters : AdvanceEnters
  iteration : LoopIteration
  stores : AdvanceStores
  tail : TailSegment

/-- What work package 3 delivers, the witness apart. -/
structure Representation : Prop where
  mapped : WindowMapped
  ofFields : WindowOfFields
  toFields : FieldsOfWindow
  fit : FieldsFit
  retained : FieldsRetained
  fieldsMapped : FieldsMapped
  mirror : MirrorFollowsSpec
  world : WorldHolds
  determined : FirstExitDetermined
  exists_ : FirstExitExists

/-! ## Small facts about the pivot -/

theorem validate_exit_mem (w : Window) (nonce : BitVec 64) : (validate w nonce).exit ∈ exits := by
  unfold validate tested exits
  repeat' split
  all_goals simp

theorem exitPC_mem (c : WG.ReplayCounter) (nonce : Nat) : exitPC c nonce ∈ exits := by
  unfold exitPC exits
  repeat' split
  all_goals simp

theorem validate_advance {w : Window} {nonce : BitVec 64} (passes : ¬Rejects w nonce)
    (ahead : w.counter < nonce + 1) :
    validate w nonce = tested (advance w (nonce + 1)) (nonce + 1) := by
  have r1 : ¬limit < w.counter := fun h => passes (.inl h)
  have r2 : ¬limit ≤ nonce := fun h => passes (.inr (.inl h))
  have r3 : ¬nonce + 0x1fc1 < w.counter := fun h => passes (.inr (.inr h))
  simp only [validate, r1, r2, r3, ahead, ↓reduceIte]

theorem validate_inside {w : Window} {nonce : BitVec 64} (passes : ¬Rejects w nonce)
    (inside : ¬w.counter < nonce + 1) :
    validate w nonce = tested w (nonce + 1) := by
  have r1 : ¬limit < w.counter := fun h => passes (.inl h)
  have r2 : ¬limit ≤ nonce := fun h => passes (.inr (.inl h))
  have r3 : ¬nonce + 0x1fc1 < w.counter := fun h => passes (.inr (.inr h))
  simp only [validate, r1, r2, r3, inside, ↓reduceIte]

theorem AtExit.kept {layout preempt kp s o e} (h : AtExit layout preempt kp s o e) :
    Kept layout preempt kp s e.machine :=
  ⟨h.carried.coverage, h.carried.rsp, h.carried.rbx, h.carried.r12, h.carried.r13,
    h.unlockArgument, h.carried.frame⟩

/-! ## The range from its segments -/

/-- The clear loop terminates: from its invariant with `i` iterations done, the
machine reaches the store of the counter. -/
theorem loop_runs (iteration : LoopIteration)
    (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64) (w : Window) (t : BitVec 64)
    (reading : Reading fetch) (context : Context layout preempt s kp skb nonce) :
    ∀ (n i : Nat) (e : Executed), top w t - i = n → AtLoop layout preempt kp s w t i e →
      Eventually (historyStep fetch) (AtStore layout preempt kp s w t) e := by
  intro n
  induction n with
  | zero =>
    intro i e measure invariant
    have := invariant.bound
    omega
  | succ n ih =>
    intro i e measure invariant
    apply eventually_trans (historyStep fetch) _ _ _
      (iteration fetch layout preempt s kp skb nonce w t i e reading context invariant)
    intro e' post
    by_cases more : i + 1 < top w t
    · simp only [more, ↓reduceIte] at post
      exact ih (i + 1) e' (by omega) post
    · simp only [more, ↓reduceIte] at post
      exact .done _ post

theorem advance_segment (enters : AdvanceEnters) (iteration : LoopIteration)
    (stores : AdvanceStores) : AdvanceSegment := by
  intro fetch layout preempt s kp skb nonce w t e reading context cut
  have toStore : Eventually (historyStep fetch) (AtStore layout preempt kp s w t) e := by
    apply eventually_trans (historyStep fetch) _ _ _
      (enters fetch layout preempt s kp skb nonce w t e reading context cut)
    intro e' post
    by_cases none : top w t = 0
    · simp only [none, ↓reduceIte] at post
      exact .done _ post
    · simp only [none, ↓reduceIte] at post
      exact loop_runs iteration fetch layout preempt s kp skb nonce w t reading context
        (top w t) 0 e' (by omega) post
  apply eventually_trans (historyStep fetch) _ _ _ toStore
  intro e' post
  exact stores fetch layout preempt s kp skb nonce w t e' reading context post

theorem range_simulates (execution : Execution) : RangeSimulates := by
  intro fetch layout preempt s kp skb nonce w reading context window
  apply eventually_trans (historyStep fetch) _ _ _
    (execution.head fetch layout preempt s kp skb nonce w reading context window)
  intro e post
  unfold HeadPost at post
  by_cases rejects : Rejects w nonce
  · simp only [rejects, ↓reduceIte] at post
    exact .done _ post
  · simp only [rejects, ↓reduceIte] at post
    by_cases ahead : w.counter < nonce + 1
    · simp only [ahead, ↓reduceIte] at post
      rw [validate_advance rejects ahead]
      apply eventually_trans (historyStep fetch) _ _ _
        (advance_segment execution.enters execution.iteration execution.stores
          fetch layout preempt s kp skb nonce w (nonce + 1) e reading context post)
      intro e' cut
      exact execution.tail fetch layout preempt s kp skb nonce _ (nonce + 1) e' reading context cut
    · simp only [ahead, ↓reduceIte] at post
      rw [validate_inside rejects ahead]
      exact execution.tail fetch layout preempt s kp skb nonce w (nonce + 1) e reading context post

/-! ## The clauses -/

theorem strong_refines (simulates : RangeSimulates) (representation : Representation) :
    StrongRefines := by
  intro fetch layout preempt s kp skb nonce world world' ambient ambient' id c result
    reading context fields held run
  obtain ⟨sameResult, sameWindow, sameExit⟩ := representation.mirror world world' ambient ambient'
    id c nonce result (representation.fit _ _ _ fields) held run
  apply eventually_weaken (historyStep fetch) _ _ _ _
    (simulates fetch layout preempt s kp skb nonce (ofCounter c) reading context
      (representation.ofFields _ _ _ fields))
  intro e h
  exact ⟨h.pc.trans sameExit.symm, h.first, h.accepted.trans sameResult.symm,
    ⟨_, sameWindow, representation.toFields _ _ _ h.carried.window⟩, h.kept, h.carried.stack⟩

/-- CLAUSE `Refines`, from the range against the pivot and the representation. -/
theorem refines_of_parts (simulates : RangeSimulates) (representation : Representation) :
    Refines := by
  intro fetch layout preempt s kp skb nonce world world' ambient ambient' id c result
    reading context fields held run
  apply eventually_weaken (historyStep fetch) _ _ _ _
    (strong_refines simulates representation fetch layout preempt s kp skb nonce world world'
      ambient ambient' id c result reading context fields held run)
  rintro e ⟨pc, first, result, window, kept, _⟩
  exact ⟨pc, first, result, window, kept⟩

/-- CLAUSE `ExitsCleanly`, from the range against the pivot: a mapped window holds
some machine window, whatever its bytes. -/
theorem exits_cleanly_of_parts (simulates : RangeSimulates) (mapped : WindowMapped) :
    ExitsCleanly := by
  intro fetch layout preempt s kp skb nonce reading context
  obtain ⟨w, window⟩ := mapped s.data.dmem kp context.window
  apply eventually_weaken (historyStep fetch) _ _ _ _
    (simulates fetch layout preempt s kp skb nonce w reading context window)
  intro e h
  exact ⟨h.pc ▸ validate_exit_mem w nonce, h.first, h.kept⟩

/-- CLAUSE `ReplayWitness`, from the refinement, the existence of first exits and the
concrete part of the witness. The second visit enters at the first visit's exit state
with the program counter put back. -/
theorem replay_witness_of_parts (strong : StrongRefines) (representation : Representation)
    (start : WitnessStart) : ReplayWitness := by
  obtain ⟨fetch, layout, preempt, s, kp, skb, nonce, world, world₁, world₂, ambient, ambient₁,
    ambient₂, id, c, reading, context, fields, held, run₁, run₂, revisit⟩ := start
  have first := strong fetch layout preempt s kp skb nonce world world₁ ambient ambient₁ id c
    true reading context fields held run₁
  have first' : Eventually (historyStep fetch)
      (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧
        (accepted e.machine = true ∧
          (∃ c', windowOf world₁ id = some c' ∧
            Layouts.ReplayFields e.machine.data.dmem (windowBase kp) c') ∧
          Kept layout preempt kp s e.machine ∧
          (∀ a, stackBytes s.data.regs.rsp.toBitVec a →
            (e.machine.data.dmem.get? a).isSome = true))) ⟨s, [s]⟩ := by
    apply eventually_weaken (historyStep fetch) _ _ _ _ first
    rintro e ⟨pc, early, result, window, kept, stack⟩
    exact ⟨pc ▸ exitPC_mem c nonce.toNat, early, result, window, kept, stack⟩
  obtain ⟨t₁, exit₁, accepted₁, ⟨c₁, held₁, fields₁⟩, kept₁, stack₁⟩ :=
    representation.exists_ fetch s
      (fun t => accepted t = true ∧
        (∃ c', windowOf world₁ id = some c' ∧
          Layouts.ReplayFields t.data.dmem (windowBase kp) c') ∧
        Kept layout preempt kp s t ∧
        (∀ a, stackBytes s.data.regs.rsp.toBitVec a → (t.data.dmem.get? a).isSome = true))
      first'
  have context₂ : Context layout (preempt + 0x200) ⟨t₁.data, Range.entry⟩ kp skb nonce :=
    revisit t₁ kept₁ stack₁ (representation.fieldsMapped _ _ _ fields₁)
  have second := strong fetch layout (preempt + 0x200) ⟨t₁.data, Range.entry⟩ kp skb nonce
    world₁ world₂ ambient₁ ambient₂ id c₁ false reading context₂ fields₁ held₁ run₂
  have second' : Eventually (historyStep fetch)
      (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧
        accepted e.machine = false) ⟨⟨t₁.data, Range.entry⟩, [⟨t₁.data, Range.entry⟩]⟩ := by
    apply eventually_weaken (historyStep fetch) _ _ _ _ second
    rintro e ⟨pc, early, result, _⟩
    exact ⟨pc ▸ exitPC_mem c₁ nonce.toNat, early, result⟩
  obtain ⟨t₂, exit₂, accepted₂⟩ :=
    representation.exists_ fetch ⟨t₁.data, Range.entry⟩ (fun t => accepted t = false) second'
  refine ⟨fetch, kp, ⟨s, t₁, nonce⟩, ⟨⟨t₁.data, Range.entry⟩, t₂, nonce⟩, reading,
    ⟨?_, ?_, ⟨fun _ _ => rfl, trivial⟩⟩, rfl, accepted₁, accepted₂,
    world, world₁, ambient, ambient₁, id, c, fields, held, run₁⟩
  · intro v member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, _, _, context⟩
    · exact ⟨_, _, _, context₂⟩
  · intro v member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · exact exit₁
    · exact exit₂

/-! ## The headline, the transported clause apart -/

/-- The three clauses that need only the mirror, from the packages' propositions. -/
theorem mirror_clauses_of_parts (execution : Execution) (representation : Representation)
    (start : WitnessStart) : ExitsCleanly ∧ Refines ∧ ReplayWitness :=
  have simulates := range_simulates execution
  ⟨exits_cleanly_of_parts simulates representation.mapped,
    refines_of_parts simulates representation,
    replay_witness_of_parts (strong_refines simulates representation) representation start⟩

/-- THE HEADLINE from its parts. `transported` is what the bridge library proves from
`Refines` and `Representation` (`Binary.C2.Bridge.no_counter_accepted_twice`). -/
theorem headline_of_parts (execution : Execution) (representation : Representation)
    (start : WitnessStart) (transported : Refines → Representation → NoCounterAcceptedTwice) :
    HeadlineRefinement :=
  have clauses := mirror_clauses_of_parts execution representation start
  ⟨clauses.1, clauses.2.1, transported clauses.2.1 representation, clauses.2.2⟩

#print axioms range_simulates
#print axioms mirror_clauses_of_parts
#print axioms headline_of_parts
end Binary.C2
