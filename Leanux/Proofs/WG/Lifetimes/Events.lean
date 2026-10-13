import Leanux.Proofs.WG.Lifetimes.Store

/-! Ordered lifetime observations. Reads and writes name the object actually
resolved; a release forbids later accesses to its identity. Slot and stamp are
separate parameters, so device epochs can be part of a future packet stamp. -/
namespace Leanux.Proofs.WG.Lifetimes

inductive AccessEvent (Slot Stamp : Type) where
  | read (slot : Slot) (stamp : Stamp)
  | write (slot : Slot) (stamp : Stamp)
  | release (slot : Slot) (stamp : Stamp)
  deriving Repr, DecidableEq

namespace AccessEvent

def Ordered : AccessEvent Slot Stamp → AccessEvent Slot Stamp → Prop
  | .release _ old, .read _ now => old ≠ now
  | .release _ old, .write _ now => old ≠ now
  | _, _ => True

def Safe (events : List (AccessEvent Slot Stamp)) : Prop := events.Pairwise Ordered

theorem Safe.take (hs : Safe h) (n : Nat) : Safe (h.take n) := by
  have whole : Safe (h.take n ++ h.drop n) := by rw [List.take_append_drop]; exact hs
  exact (List.pairwise_append.mp whole).1

def Released (events : List (AccessEvent Slot Stamp)) (stamp : Stamp) : Prop :=
  ∃ slot, .release slot stamp ∈ events

@[simp] theorem released_append :
    Released (h ++ g) stamp ↔ Released h stamp ∨ Released g stamp := by
  simp only [Released, List.mem_append, exists_or]

theorem safe_nil : Safe ([] : List (AccessEvent Slot Stamp)) := List.Pairwise.nil

theorem safe_append_read (hs : Safe h) (hn : ¬ Released h stamp) :
    Safe (h ++ [.read slot stamp]) := by
  apply List.pairwise_append.mpr
  refine ⟨hs, by simp, ?_⟩
  intro e he b hb
  simp only [List.mem_singleton] at hb
  subst b
  cases e with
  | read _ _ => trivial
  | write _ _ => trivial
  | release i old =>
    intro hid
    subst old
    exact hn ⟨i, he⟩

theorem safe_append_write (hs : Safe h) (hn : ¬ Released h stamp) :
    Safe (h ++ [.write slot stamp]) := by
  apply List.pairwise_append.mpr
  refine ⟨hs, by simp, ?_⟩
  intro e he b hb
  simp only [List.mem_singleton] at hb
  subst b
  cases e with
  | read _ _ => trivial
  | write _ _ => trivial
  | release i old =>
    intro hid
    subst old
    exact hn ⟨i, he⟩

theorem safe_append_release (hs : Safe h) : Safe (h ++ [.release slot stamp]) := by
  apply List.pairwise_append.mpr
  refine ⟨hs, by simp, ?_⟩
  intro e _ b hb
  simp only [List.mem_singleton] at hb
  subst b
  cases e <;> trivial

@[simp] theorem released_append_read :
    Released (h ++ [.read slot value]) stamp ↔ Released h stamp := by
  simp [Released]

@[simp] theorem released_append_write :
    Released (h ++ [.write slot value]) stamp ↔ Released h stamp := by
  simp [Released]

@[simp] theorem released_append_release :
    Released (h ++ [.release slot value]) stamp ↔ Released h stamp ∨ stamp = value := by
  simp only [Released, List.mem_append, List.mem_singleton, AccessEvent.release.injEq,
    exists_or]
  simp [eq_comm]

end AccessEvent
end Leanux.Proofs.WG.Lifetimes
