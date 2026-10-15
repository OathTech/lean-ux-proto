import PeerCountState
import TrustBase
import History

namespace Binary.PeerCountPhase

private theorem restore_history {history : List MachineState} {s : MachineState}
    (last : history.getLast? = some s) : history.dropLast ++ [s] = history := by
  have nonempty : history ≠ [] := by intro empty; rw [empty] at last; cases last
  have lastEq : history.getLast nonempty = s := by
    simpa only [List.getLast?_eq_some_getLast nonempty, Option.some.injEq] using last
  rw [← lastEq]
  exact List.dropLast_concat_getLast nonempty

theorem scan_splice (pending : Option Pending) (front : List MachineState)
    (shared : MachineState) (back : List MachineState) :
    scan pending (front ++ shared :: back) = scan (scan pending (front ++ [shared])) (shared :: back) := by
  induction front generalizing pending with
  | nil => rfl
  | cons before front ih =>
    cases front with
    | nil => rfl
    | cons after front =>
      simpa only [List.cons_append, scan] using ih (edge pending before after)

theorem scan_snoc (pending : Option Pending) (history : List MachineState)
    (before after : MachineState) (last : history.getLast? = some before) :
    scan pending (history ++ [after]) = edge (scan pending history) before after := by
  have restored := restore_history last
  rw [← restored]
  rw [List.append_assoc, List.singleton_append]
  exact scan_splice pending history.dropLast before [after]

theorem scan_append (pending : Option Pending) (history : List MachineState)
    (before : MachineState) (tail : List MachineState) (last : history.getLast? = some before) :
    scan pending (history ++ tail) = scan (scan pending history) (before :: tail) := by
  rw [← restore_history last, List.append_assoc, List.singleton_append]
  exact scan_splice pending history.dropLast before tail

theorem edge_silent (pending : Option Pending) (before after : MachineState)
    (outside : Image.fetch before.pc = none) : edge pending before after = pending := by
  have noReturn : before.pc ≠ Image.PeerGet.entry+0xaf := by
    intro equal
    rw [equal] at outside
    cases outside
  have noIncrement : before.pc ≠ Image.PeerGet.entry+0x4a := by
    intro equal
    rw [equal] at outside
    cases outside
  simp only [edge, noReturn, ite_false, noIncrement, false_and]

/-- Named service contracts retain all their states. Their no-reentry
    condition proves that those edges cannot reset or fabricate this phase. -/
theorem scan_service (pending : Option Pending) (history : List MachineState)
    (outside : TrustBase.NoAnchoredReentry history) : scan pending history = pending := by
  induction history generalizing pending with
  | nil => rfl
  | cons before rest ih =>
    cases rest with
    | nil => rfl
    | cons after rest =>
      have first : Image.fetch before.pc = none := outside before (by simp)
      have tail : TrustBase.NoAnchoredReentry (after :: rest) := by
        intro s member
        exact outside s (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact Or.inr member)
      simp only [scan, edge_silent pending before after first]
      exact ih pending tail

/-- Ordinary instructions leave the pending count unchanged. Both trigger
    PCs are checked explicitly; absence of correspondence cuts is not enough. -/
theorem edge_ordinary (pending : Option Pending) (before after : MachineState)
    (noReturn : before.pc ≠ Image.PeerGet.entry+0xaf)
    (noIncrement : before.pc ≠ Image.PeerGet.entry+0x4a) :
    edge pending before after = pending := by
  simp only [edge, noReturn, ite_false, noIncrement, false_and]

/-- A real CALL followed by the named service's no-reentry history preserves
    the pending count phase, including all of the service's internal states. -/
theorem scan_call_service (pending : Option Pending) (front : List MachineState)
    (before called : MachineState) (tail : List MachineState)
    (noReturn : before.pc ≠ Image.PeerGet.entry+0xaf)
    (noIncrement : before.pc ≠ Image.PeerGet.entry+0x4a)
    (service : TrustBase.NoAnchoredReentry (called :: tail)) :
    scan pending (front ++ before :: called :: tail) = scan pending (front ++ [before]) := by
  rw [scan_splice pending front before (called :: tail)]
  change scan (edge (scan pending (front ++ [before])) before called) (called :: tail) = _
  rw [edge_ordinary _ before called noReturn noIncrement]
  exact scan_service _ _ service


/-- A suffix that preserves the count scanner at every actual prefix,
    including service interiors. The seed is the incoming scanner state,
    rather than an independently supplied source count. -/
def StableExtension (before after : List MachineState) : Prop :=
  ∃ tail, after = before ++ tail ∧ ∀ seed n,
    scan seed (before ++ tail.take n) = scan seed before

theorem StableExtension.refl (history : List MachineState) : StableExtension history history :=
  ⟨[], by simp, by simp⟩

theorem StableExtension.prefix {before after : List MachineState}
    (h : StableExtension before after) : before.IsPrefix after := by
  obtain ⟨tail, recorded, _⟩ := h
  exact ⟨tail, recorded.symm⟩

theorem StableExtension.final {before after : List MachineState}
    (h : StableExtension before after) (seed : Option Pending) :
    scan seed after = scan seed before := by
  obtain ⟨tail, recorded, stable⟩ := h
  simpa only [List.take_length, ← recorded] using stable seed tail.length

theorem StableExtension.trans {first middle last : List MachineState}
    (a : StableExtension first middle) (b : StableExtension middle last) :
    StableExtension first last := by
  obtain ⟨left, middleEq, leftStable⟩ := a
  obtain ⟨right, lastEq, rightStable⟩ := b
  refine ⟨left ++ right, by rw [lastEq, middleEq, List.append_assoc], ?_⟩
  intro seed n
  by_cases small : n ≤ left.length
  · simpa only [List.take_append_of_le_length small] using leftStable seed n
  · have large : left.length ≤ n := by omega
    rw [List.take_append, List.take_of_length_le large, ← List.append_assoc, ← middleEq]
    rw [rightStable]
    simpa only [List.take_length, ← middleEq] using leftStable seed left.length

def Ordinary (s : MachineState) : Prop :=
  s.pc ≠ Image.PeerGet.entry+0xaf ∧ s.pc ≠ Image.PeerGet.entry+0x4a

theorem scan_ordinary (seed : Option Pending) (history : List MachineState)
    (ordinary : ∀ s ∈ history.dropLast, Ordinary s) : scan seed history = seed := by
  induction history generalizing seed with
  | nil => rfl
  | cons before rest ih =>
    cases rest with
    | nil => rfl
    | cons after rest =>
      have current := ordinary before (by simp)
      change scan (edge seed before after) (after :: rest) = seed
      rw [edge_ordinary _ _ _ current.1 current.2]
      apply ih
      intro s member
      exact ordinary s (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact .inr member)

/-- Dropping a suffix never adds a new source PC to a scanned edge. -/
theorem ordinary_take (history : List MachineState) (n : Nat)
    (ordinary : ∀ s ∈ history.dropLast, Ordinary s) :
    ∀ s ∈ (history.take n).dropLast, Ordinary s := by
  intro s member
  apply ordinary s
  have length : ((history.take n).dropLast).length ≤ history.dropLast.length := by simp; omega
  have prefixed : (history.take n).dropLast <+: history.dropLast := by
    rw [List.dropLast_eq_take, List.dropLast_eq_take, List.take_take]
    apply List.take_prefix_take_left
    simp
    omega
  exact List.IsPrefix.subset prefixed member

theorem StableExtension.of_ordinary (front : List MachineState) (current : MachineState)
    (tail : List MachineState)
    (ordinary : ∀ s ∈ (current :: tail).dropLast, Ordinary s) :
    StableExtension (front ++ [current]) (front ++ current :: tail) := by
  refine ⟨tail, by simp, ?_⟩
  intro seed n
  rw [List.append_assoc, List.singleton_append, scan_splice]
  apply scan_ordinary
  have reduced := ordinary_take (current :: tail) (n+1) ordinary
  simpa only [List.take_succ_cons] using reduced

theorem StableExtension.call (front : List MachineState) (before called : MachineState)
    (tail : List MachineState) (ordinary : Ordinary before)
    (service : TrustBase.NoAnchoredReentry (called :: tail)) :
    StableExtension (front ++ [before]) (front ++ before :: called :: tail) := by
  apply StableExtension.of_ordinary
  intro s member
  simp only [List.dropLast_cons_cons, List.mem_cons] at member
  rcases member with equal | inside
  · subst s; exact ordinary
  · have outside := service s inside
    constructor <;> intro eq <;> rw [eq] at outside <;> cases outside

theorem StableExtension.service (front : List MachineState) (called : MachineState)
    (tail : List MachineState) (service : TrustBase.NoAnchoredReentry (called :: tail)) :
    StableExtension (front ++ [called]) (front ++ called :: tail) := by
  apply StableExtension.of_ordinary
  intro s member
  have outside := service s member
  constructor <;> intro eq <;> rw [eq] at outside <;> cases outside

/-- A suffix preserves the pending count until its final RET successor,
    which clears it. Its strictly nonempty executed suffix distinguishes
    the return from a zero-instruction postcondition. -/
def ReturningExtension (before after : List MachineState) : Prop :=
  ∃ tail, tail ≠ [] ∧ after = before ++ tail ∧ ∀ seed n,
    scan seed (before ++ tail.take n) =
      if n < tail.length then scan seed before else none

theorem ReturningExtension.final {before after : List MachineState}
    (h : ReturningExtension before after) (seed : Option Pending) : scan seed after = none := by
  obtain ⟨tail, _, recorded, phase⟩ := h
  simpa only [List.take_length, Nat.lt_irrefl, ite_false, ← recorded] using phase seed tail.length

theorem ReturningExtension.none_prefix {before after : List MachineState}
    (h : ReturningExtension before after) (initial : scan none before = none) :
    ∀ n, before.length ≤ n → scan none (after.take n) = none := by
  obtain ⟨tail, _, recorded, phase⟩ := h
  intro n bound
  rw [recorded, List.take_append, List.take_of_length_le bound, phase, initial]
  split <;> rfl

theorem StableExtension.returning {first middle last : List MachineState}
    (a : StableExtension first middle) (b : ReturningExtension middle last) :
    ReturningExtension first last := by
  obtain ⟨left, middleEq, leftStable⟩ := a
  obtain ⟨right, nonempty, lastEq, rightPhase⟩ := b
  refine ⟨left ++ right, by simp [nonempty], by rw [lastEq, middleEq, List.append_assoc], ?_⟩
  intro seed n
  have positive : 0 < right.length := List.length_pos_iff.mpr nonempty
  by_cases small : n ≤ left.length
  · rw [List.take_append_of_le_length small, leftStable]
    simp only [List.length_append, show n < left.length+right.length by omega, ite_true]
  · have large : left.length ≤ n := by omega
    rw [List.take_append, List.take_of_length_le large, ← List.append_assoc, ← middleEq, rightPhase]
    have old : scan seed middle = scan seed first := by
      simpa only [List.take_length, ← middleEq] using leftStable seed left.length
    rw [old]
    have same : n-left.length < right.length ↔ n < (left++right).length := by simp; omega
    simp only [same]

#print axioms scan_append
#print axioms ReturningExtension.final
#print axioms ReturningExtension.none_prefix
#print axioms StableExtension.returning
#print axioms StableExtension.trans
#print axioms StableExtension.of_ordinary
#print axioms StableExtension.call
end Binary.PeerCountPhase
