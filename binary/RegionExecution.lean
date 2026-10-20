import Execution

namespace Binary

private theorem load_mono (s : MachineData) (a : BitVec 64) (w : Width)
    (k l : w.type → MachineData → Effects) (P Q : MachineState → Prop)
    (h : ∀ v d, (k v d).All P → (l v d).All Q) :
    (s.load a w k).All P → (s.load a w l).All Q := by
  simp only [MachineData.load, Effects.All]
  split
  · apply h
  · exact False.elim

private theorem store_mono (s : MachineData) (a : BitVec 64) {w : Width} (v : w.type)
    (k l : MachineData → Effects) (P Q : MachineState → Prop)
    (h : ∀ d, (k d).All P → (l d).All Q) :
    (s.store a v k).All P → (s.store a v l).All Q := by
  simp only [MachineData.store, Effects.All]
  split
  · apply h
  · exact False.elim

private theorem set_mono [Labels] [AddressSize] (s : MachineData) {w : Width}
    (dst : Dst w) (v : w.type) (p : Std.Rco Int64)
    (k l : MachineData → Effects) (P Q : MachineState → Prop)
    (h : ∀ d, (k d).All P → (l d).All Q) :
    (s.set dst v p k).All P → (s.set dst v p l).All Q := by
  cases dst with
  | reg r => exact h _
  | mem a => exact store_mono _ _ _ _ _ _ _ h

private theorem regmem_mono [Labels] [AddressSize] {w : Width}
    (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    (k l : w.type → MachineData → Effects) (P Q : MachineState → Prop)
    (h : ∀ v d, (k v d).All P → (l v d).All Q) :
    (o.interp s p k).All P → (o.interp s p l).All Q := by
  cases o with
  | reg r => exact h _ _
  | mem a => exact load_mono _ _ _ _ _ _ _ h

private theorem operand_mono [Labels] [AddressSize] {w : Width}
    (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
    (k l : w.type → MachineData → Effects) (P Q : MachineState → Prop)
    (h : ∀ v d, (k v d).All P → (l v d).All Q) :
    (o.interp s p k).All P → (o.interp s p l).All Q := by
  cases o with
  | regOrMem r => exact regmem_mono _ _ _ _ _ _ _ h
  | imm v => exact h _ _

private theorem target_mono [Labels] [AddressSize]
    (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
    (k l : BitVec 64 → MachineData → Effects) (P Q : MachineState → Prop)
    (h : ∀ v d, (k v d).All P → (l v d).All Q) :
    (o.interp s p k).All P → (o.interp s p l).All Q := by
  cases o with
  | rel c => exact h _ _
  | reg r => exact h _ _
  | mem a => exact load_mono _ _ _ _ _ _ _ h

/-- Operations encountered in the two decoded functions. This is a proof
    convenience, not a change to the ISA or an entry-state restriction. -/
def RegionOperation {w} : Operation w → Prop
  | .mov .. | .movzx .. | .movsx .. | .push .. | .pop .. | .setcc .. | .lea ..
  | .add .. | .sub .. | .cmp .. | .cmpxchg .. | .test ..
  | .and .. | .or .. | .not .. | .shr .. | .shl .. | .bt .. | .xor .. | .bsr .. | .bswap .. | .cmovcc .. | .sar .. | .jcc .. | .jmp .. | .call .. | .ret => True
  | _ => False

theorem operation_mono [Labels] [AddressSize] {w} (i : Operation w)
    (supported : RegionOperation i) (s : MachineData) (p : Std.Rco Int64)
    (next₁ next₂ : MachineData → Effects)
    (jump₁ jump₂ : Int64 → MachineData → Effects) (P Q : MachineState → Prop)
    (hn : ∀ d, (next₁ d).All P → (next₂ d).All Q)
    (hj : ∀ pc d, (jump₁ pc d).All P → (jump₂ pc d).All Q) :
    (i.interp p s next₁ jump₁).All P → (i.interp p s next₂ jump₂).All Q := by
  cases i <;> simp only [RegionOperation] at supported
  all_goals try contradiction
  all_goals simp only [Operation.interp]
  all_goals repeat first
    | contradiction
    | exact hn _
    | exact hj _ _
    | apply operand_mono; intro _ _
    | apply regmem_mono; intro _ _
    | apply target_mono; intro _ _
    | apply load_mono; intro _ _
    | apply store_mono; intro _
    | apply set_mono; intro _
    | (change (∀ _, _) → (∀ _, _); intro h v; specialize h v; revert h)
    | split
    | exact False.elim

/-- Separate fallthrough and jump continuations: a jump to the next address
    still exits a region. -/
def CpsMono [Labels] (i : Instr) : Prop :=
  ∀ (s : MachineData) (p : Std.Rco Int64)
    (next₁ next₂ : MachineData → Effects)
    (jump₁ jump₂ : Int64 → MachineData → Effects) (P Q : MachineState → Prop),
    (∀ d, (next₁ d).All P → (next₂ d).All Q) →
    (∀ pc d, (jump₁ pc d).All P → (jump₂ pc d).All Q) →
    (i.interp s p next₁ jump₁).All P → (i.interp s p next₂ jump₂).All Q

theorem regular_mono [Labels] (addr w : Width) (op : Operation w)
    (supported : RegionOperation op) : CpsMono (.regular addr w op) := by
  intro s p n₁ n₂ j₁ j₂ P Q hn hj
  exact @operation_mono _ ⟨addr⟩ _ op supported s p n₁ n₂ j₁ j₂ P Q hn hj

inductive LaidOut [Labels] (fetch : Int64 → Option Decoded) :
    Int64 → List (Kraken.Sized Directive) → Prop
  | nil (pc) : LaidOut fetch pc []
  | cons (pc : Int64) (i : Instr) (n : Nat) (tail : List (Kraken.Sized Directive))
      (positive : 0 < n) (here : fetch pc = some ⟨i, n⟩) (mono : CpsMono i)
      (rest : LaidOut fetch (pc + .ofNat n) tail) :
      LaidOut fetch pc (⟨.instr i, n⟩ :: tail)

theorem LaidOut.agreement [Labels] {fetch full pc code}
    (layout : LaidOut fetch pc code)
    (agree : ∀ p i, fetch p = some i → full p = some i) : LaidOut full pc code := by
  induction layout with
  | nil pc => exact .nil pc
  | cons pc i n tail positive here mono rest ih =>
    exact .cons pc i n tail positive (agree _ _ here) mono ih

/-- Region symbolic execution entails execution of each fetched instruction.
    The layout witness connects every instruction and length to the image. -/
theorem region_eventually [Labels] {fetch pc code}
    (layout : LaidOut fetch pc code) (s : MachineData) (P : MachineState → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d, p⟩)).All P) :
    Eventually (instructionStep fetch) P ⟨s, pc⟩ := by
  induction layout generalizing s with
  | nil pc => exact .done _ run
  | cons pc i n tail positive here mono rest ih =>
    apply step_cps
    simp only [instructionStep, here]
    refine ⟨positive, ?_⟩
    apply mono s ⟨pc, pc + .ofNat n⟩
      (fun d => Directives.interp tail d (pc + .ofNat n) (fun p d => .done ⟨d, p⟩))
      _ (fun p d => .done ⟨d, p⟩) _ P _
    · exact fun d h => ih d h
    · exact fun p d h => .done _ h
    · exact run

#print axioms operation_mono
#print axioms region_eventually
end Binary
