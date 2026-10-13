import Leanux.WG.State

/-! Allocation identities, independent of the contents held in a slot. A
transition may remove an identity or allocate beyond its starting frontier;
an old identity still present at the end must have occupied the same slot. -/
namespace Leanux.Proofs.WG.Lifetimes

@[ext] structure Store (Slot : Type) where
  frontier : Nat
  slots : Slot → Option Nat

def Bounded (s : Store Slot) : Prop :=
  ∀ i stamp, s.slots i = some stamp → stamp ≤ s.frontier

def Absent (s : Store Slot) (stamp : Nat) : Prop :=
  ∀ i, s.slots i ≠ some stamp

def Transition (s t : Store Slot) : Prop :=
  s.frontier ≤ t.frontier ∧
  ∀ i stamp, t.slots i = some stamp → stamp ≤ s.frontier → s.slots i = some stamp

/-- A helper that only retains or removes identities; allocation is separate. -/
def Retained (s t : Store Slot) : Prop :=
  t.frontier = s.frontier ∧
  ∀ i stamp, t.slots i = some stamp → s.slots i = some stamp

theorem Retained.refl (s : Store Slot) : Retained s s := ⟨rfl, fun _ _ h => h⟩

theorem Retained.trans (h : Retained s t) (g : Retained t u) : Retained s u :=
  ⟨g.1.trans h.1, fun i stamp hi => h.2 i stamp (g.2 i stamp hi)⟩

theorem Retained.transition (h : Retained s t) : Transition s t :=
  ⟨by rw [h.1]; exact Nat.le_refl _, fun i stamp hi _ => h.2 i stamp hi⟩

theorem Retained.bounded (h : Retained s t) (hb : Bounded s) : Bounded t := by
  intro i stamp hi
  rw [h.1]
  exact hb i stamp (h.2 i stamp hi)

theorem Transition.refl (s : Store Slot) : Transition s s :=
  ⟨Nat.le_refl _, fun _ _ h _ => h⟩

theorem Transition.trans (h : Transition s t) (g : Transition t u) : Transition s u :=
  ⟨Nat.le_trans h.1 g.1, fun i stamp hu hb =>
    h.2 i stamp (g.2 i stamp hu (Nat.le_trans hb h.1)) hb⟩

theorem Transition.absent (h : Transition s t) (hb : stamp ≤ s.frontier)
    (ha : Absent s stamp) : Absent t stamp :=
  fun i hi => ha i (h.2 i stamp hi hb)

theorem Transition.empty_fresh (h : Transition s t) (hi : s.slots i = none)
    (ht : t.slots i = some stamp) : s.frontier < stamp := by
  by_cases hb : stamp ≤ s.frontier
  · have := h.2 i stamp ht hb
    simp [hi] at this
  · omega

theorem Transition.released (h : Transition s t) (g : Transition t u)
    (hb : Bounded s) (hi : s.slots i = some stamp) (ha : Absent t stamp) :
    Absent u stamp :=
  g.absent (Nat.le_trans (hb i stamp hi) h.1) ha

def Store.put [DecidableEq Slot] (s : Store Slot) (i : Slot) (value : Option Nat) : Store Slot :=
  { s with slots := fun j => if j = i then value else s.slots j }

def Store.allocate [DecidableEq Slot] (s : Store Slot) (i : Slot) : Store Slot :=
  { frontier := s.frontier + 1,
    slots := fun j => if j = i then some (s.frontier + 1) else s.slots j }

theorem put_existing [DecidableEq Slot] (s : Store Slot) (i : Slot)
    (h : s.slots i = value) : s.put i value = s := by
  apply Store.ext
  · rfl
  · funext j; by_cases hj : j = i <;> simp [Store.put, hj, h]

theorem erase_transition [DecidableEq Slot] (s : Store Slot) (i : Slot) :
    Transition s (s.put i none) := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro j stamp hj _
  by_cases h : j = i <;> simp_all [Store.put]

theorem erase_retained [DecidableEq Slot] (s : Store Slot) (i : Slot) :
    Retained s (s.put i none) := by
  refine ⟨rfl, ?_⟩
  intro j stamp hj
  by_cases h : j = i <;> simp_all [Store.put]

theorem erase_bounded [DecidableEq Slot] (s : Store Slot) (i : Slot)
    (hb : Bounded s) : Bounded (s.put i none) := by
  exact (erase_retained s i).bounded hb

theorem allocate_transition [DecidableEq Slot] (s : Store Slot) (i : Slot) :
    Transition s (s.allocate i) := by
  refine ⟨by simp [Store.allocate], ?_⟩
  intro j stamp hj hb
  by_cases h : j = i
  · simp [Store.allocate, h] at hj
    omega
  · simpa [Store.allocate, h] using hj

theorem allocate_bounded [DecidableEq Slot] (s : Store Slot) (i : Slot)
    (hb : Bounded s) : Bounded (s.allocate i) := by
  intro j stamp hj
  by_cases h : j = i
  · simp [Store.allocate, h] at hj
    simp [Store.allocate, ← hj]
  · have := hb j stamp (by simpa [Store.allocate, h] using hj)
    simp only [Store.allocate]
    omega

end Leanux.Proofs.WG.Lifetimes
