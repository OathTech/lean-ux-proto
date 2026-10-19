import Leanux.Proofs.WG.CounterWindow.MirrorCalls

/-! The replay bitmap has no marked future bits in its current word. This
property is stronger than remembering past acceptances: it makes a rejected
test-and-set idempotent. It holds for a fresh counter and every native-model
step; arbitrary shape-correct bitmaps are deliberately not assumed coherent. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayRefusal
open Leanux Leanux.WG CounterWindow

def Coherent (c : ReplayCounter) : Prop :=
  c.backtrack.size = 128 ∧
    ∀ b, c.counter % 64 < b → c.backtrack[slot c.counter]!.testBit b = false

private theorem one_bit (i : Nat) : (1 : Nat).testBit i = decide (i = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.testBit_one_eq_true_iff_self_eq_zero,decide_eq_true_eq]

private theorem clear_keeps_zero (a : Array Nat) (current j : Nat) (xs : List Nat)
    (zero : a[j]! = 0) : (clear a current xs)[j]! = 0 := by
  induction xs generalizing a with
  | nil => exact zero
  | cons i rest ih =>
    apply ih
    by_cases same : (i + current) % 128 = j
    · subst j
      by_cases bound : (i + current) % 128 < a.size
      · rw [Array.getElem!_set!_self _ _ _ bound]
      · simp [Array.set!,bound]
    · rw [Array.getElem!_set!_ne _ _ _ _ same]
      exact zero

private theorem clear_zero_of_mem (a : Array Nat) (current j : Nat) (xs : List Nat)
    (bound : j < a.size) (hit : ∃ i ∈ xs, (i + current) % 128 = j) :
    (clear a current xs)[j]! = 0 := by
  induction xs generalizing a with
  | nil => simp at hit
  | cons i rest ih =>
    change (clear (a.set! ((i + current) % 128) 0) current rest)[j]! = 0
    obtain ⟨k,member,same⟩ := hit
    rcases List.mem_cons.mp member with rfl | member
    · apply clear_keeps_zero
      rw [same,Array.getElem!_set!_self _ _ _ bound]
    · apply ih
      · simpa using bound
      · exact ⟨k,member,same⟩

private theorem advancing_word_zero (c : ReplayCounter) (n : Nat)
    (shape : c.backtrack.size = 128) (later : c.counter / 64 < n / 64) :
    (prepared c n)[slot n]! = 0 := by
  have advances : n > c.counter := by omega
  rw [prepared,ite_eq_left advances]
  apply clear_zero_of_mem
  · simp only [shape,slot]
    omega
  · let i := (n / 64 - c.counter / 64 - 1) % 128 + 1
    refine ⟨i,?_,?_⟩
    · apply List.mem_range'.mpr
      refine ⟨i - 1,?_,by omega⟩
      dsimp [i]
      omega
    · dsimp [i,slot]
      omega

private theorem prepared_future (c : ReplayCounter) (n b : Nat) (hi : Coherent c)
    (later : c.counter < n) (future : n % 64 ≤ b) :
    (prepared c n)[slot n]!.testBit b = false := by
  by_cases word : c.counter / 64 = n / 64
  · have slotEq : slot n = slot c.counter := by simp only [slot,word]
    rw [prepared,ite_eq_left later]
    have count : min (n / 64 - c.counter / 64) 128 = 0 := by omega
    simp only [count,List.range'_zero,clear,slotEq]
    exact hi.2 b (by omega)
  · rw [advancing_word_zero c n hi.1 (by omega)]
    simp

theorem coherent_empty : Coherent ({} : ReplayCounter) := by
  constructor
  · rfl
  · intro b _
    simp [slot]

theorem coherent_update (c : ReplayCounter) (nonce : Nat) (hi : Coherent c)
    (eligible : CounterWindow.eligible c nonce) : Coherent (update c nonce) := by
  refine ⟨by simpa only [update_size] using hi.1,?_⟩
  intro b future
  by_cases later : c.counter < nonce + 1
  · have top : max c.counter (nonce + 1) = nonce + 1 := Nat.max_eq_right (by omega)
    simp only [update,top] at future ⊢
    rw [Array.getElem!_set!_self]
    · simp only [Nat.testBit_or,prepared_future c (nonce + 1) b hi later (by omega),
        Bool.false_or,Nat.testBit_shiftLeft]
      have beyond : bit (nonce + 1) < b := by exact future
      simp only [one_bit]
      simp
      omega
    · simp only [prepared_size,hi.1,slot]
      omega
  · have top : max c.counter (nonce + 1) = c.counter := Nat.max_eq_left (by omega)
    simp only [update,top,prepared,ite_eq_right later] at future ⊢
    by_cases same : slot (nonce + 1) = slot c.counter
    · rw [←same,Array.getElem!_set!_self]
      · have pastBit : bit (nonce + 1) ≤ c.counter % 64 := by
          dsimp [slot] at same
          dsimp [bit]
          have lower := eligible.2.2
          omega
        have old := hi.2 b future
        rw [←same] at old
        simp only [Nat.testBit_or,old,Bool.false_or,Nat.testBit_shiftLeft]
        simp only [one_bit]
        simp
        omega
      · simp only [hi.1,slot]
        omega
    · rw [Array.getElem!_set!_ne _ _ _ _ same]
      exact hi.2 b future

theorem coherent_step (c : ReplayCounter) (nonce : Nat) (hi : Coherent c) :
    Coherent (step c nonce).2 := by
  unfold step
  split
  · exact coherent_update c nonce hi ‹_›
  · exact hi

private theorem already_set (word b : Nat) (marked : word.testBit b = true) :
    word ||| (1 <<< b) = word := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases same : i = b
  · subst i
    simp [marked,Nat.testBit_shiftLeft]
  · simp only [Nat.testBit_or,Nat.testBit_shiftLeft]
    simp only [one_bit]
    have mask : (decide (b ≤ i) && decide (i - b = 0)) = false := by simp; omega
    rw [mask,Bool.or_false]

theorem rejected_unchanged (c : ReplayCounter) (nonce : Nat) (hi : Coherent c)
    (refused : (step c nonce).1 = false) : (step c nonce).2 = c := by
  unfold step at refused ⊢
  split
  · rename_i eligible
    simp only [ite_eq_left eligible] at refused
    have laterFalse : ¬ c.counter < nonce + 1 := by
      intro later
      have fresh := prepared_future c (nonce + 1) (bit (nonce + 1)) hi later (Nat.le_refl _)
      simp only [CounterWindow.fresh,fresh,Bool.not_false] at refused
      cases refused
    have top : max c.counter (nonce + 1) = c.counter := Nat.max_eq_left (by omega)
    have prep : prepared c (nonce + 1) = c.backtrack := by simp [prepared,laterFalse]
    have marked : c.backtrack[slot (nonce + 1)]!.testBit (bit (nonce + 1)) = true := by
      cases marked : c.backtrack[slot (nonce + 1)]!.testBit (bit (nonce + 1)) <;> simp_all only [fresh,Bool.not_false,Bool.not_true]
    simp only [update,top,prep,already_set _ _ marked]
    have bound : slot (nonce + 1) < c.backtrack.size := by simp only [hi.1,slot]; omega
    simp [Array.set!,Array.setIfInBounds,bound]
  · rfl

theorem coherent_finish (c : ReplayCounter) (nonces : List Nat) (hi : Coherent c) :
    Coherent (finish c nonces) := by
  induction nonces generalizing c with
  | nil => exact hi
  | cons nonce rest ih => exact ih _ (coherent_step c nonce hi)

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayRefusal
