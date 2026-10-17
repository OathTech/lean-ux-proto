import Leanux.WG.RxData
import Init.Data.Range.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

/-!
A pure, word-indexed presentation of receive.c's counter_validate.
The one-based counter and inclusive old-packet boundary are intentional.
This file does not alter the executable mirror.
-/
namespace Leanux.Proofs.WG.CounterWindow
open Leanux Leanux.WG

/-- Circular bitmap slot of a one-based message counter. -/
def slot (n : Nat) : Nat := n / 64 % 128

/-- In-word bit of a one-based message counter. -/
def bit (n : Nat) : Nat := n % 64

/-- Clear exactly the words the C loop visits, in the same order. -/
def clear (a : Array Nat) (current : Nat) : List Nat → Array Nat
  | [] => a
  | i :: rest => clear (a.set! ((i + current) % 128) 0) current rest

/-- The bitmap after advancing, before test_and_set_bit. -/
def prepared (c : ReplayCounter) (n : Nat) : Array Nat :=
  if n > c.counter then
    clear c.backtrack (c.counter / 64)
      (List.range' 1 (min (n / 64 - c.counter / 64) 128))
  else c.backtrack

/-- C's three early rejection conditions, expressed using the wire nonce. -/
abbrev eligible (c : ReplayCounter) (nonce : Nat) : Prop :=
  c.counter < REJECT_AFTER_MESSAGES + 1 ∧
  nonce < REJECT_AFTER_MESSAGES ∧
  c.counter ≤ 8128 + (nonce + 1)

def fresh (c : ReplayCounter) (nonce : Nat) : Bool :=
  !(prepared c (nonce + 1))[slot (nonce + 1)]!.testBit (bit (nonce + 1))

/-- C updates even when test_and_set_bit finds an existing bit. -/
def update (c : ReplayCounter) (nonce : Nat) : ReplayCounter :=
  let n := nonce + 1
  let a := prepared c n
  { counter := max c.counter n
    backtrack := a.set! (slot n) (a[slot n]! ||| (1 <<< bit n)) }

/-- A pure window call. Malformed arrays are excluded by the refinement's
shape premise; this definition is only an arithmetic/bitmap model. -/
def step (c : ReplayCounter) (nonce : Nat) : Bool × ReplayCounter :=
  if eligible c nonce then (fresh c nonce, update c nonce) else (false, c)

@[simp] theorem clear_size (a : Array Nat) (current : Nat) (xs : List Nat) :
    (clear a current xs).size = a.size := by
  induction xs generalizing a with
  | nil => rfl
  | cons i rest ih => simpa [clear] using ih (a.set! ((i + current) % 128) 0)

@[simp] theorem prepared_size (c : ReplayCounter) (n : Nat) :
    (prepared c n).size = c.backtrack.size := by
  unfold prepared
  split <;> simp

@[simp] theorem update_size (c : ReplayCounter) (nonce : Nat) :
    (update c nonce).backtrack.size = c.backtrack.size := by
  simp [update]

/-- Circular reuse cannot clear an old counter which remains in the window.
All divisions and moduli here have fixed, concrete divisors. -/
theorem live_slot_not_cleared (p high n i : Nat)
    (hp : p ≤ high) (hlive : n ≤ p + 8128)
    (hi : 1 ≤ i) (hitop : i ≤ n / 64 - high / 64) :
    (i + high / 64) % 128 ≠ slot p := by
  unfold slot
  omega

theorem clear_get_preserved (a : Array Nat) (current j : Nat) (xs : List Nat)
    (h : ∀ i ∈ xs, (i + current) % 128 ≠ j) :
    (clear a current xs)[j]! = a[j]! := by
  induction xs generalizing a with
  | nil => rfl
  | cons i rest ih =>
    simp only [clear]
    rw [ih _ (by intro k hk; exact h k (by simp [hk]))]
    exact Array.getElem!_set!_ne _ _ _ _ (h i (by simp))

/-- In-window bits already set are preserved by the advancing clear loop. -/
theorem prepared_get_live (c : ReplayCounter) (p n : Nat)
    (hp : p ≤ c.counter) (hlive : n ≤ p + 8128) :
    (prepared c n)[slot p]! = c.backtrack[slot p]! := by
  unfold prepared
  split
  · apply clear_get_preserved
    intro i hi
    have hr := List.mem_range'.mp hi
    obtain ⟨k, hk, rfl⟩ := hr
    apply live_slot_not_cleared p c.counter n (1 + 1 * k) hp hlive <;> omega
  · rfl

/-- Bit setting preserves every old bit. -/
theorem testBit_or_preserves (word mask b : Nat) (h : word.testBit b = true) :
    (word ||| mask).testBit b = true := by simp [h]

/-- The selected bit is set by test_and_set_bit. -/
theorem testBit_set_self (word b : Nat) :
    (word ||| (1 <<< b)).testBit b = true := by
  simp [Nat.testBit_shiftLeft]

/-- The one-based highest counter never decreases. -/
theorem step_counter_mono (c : ReplayCounter) (nonce : Nat) :
    c.counter ≤ (step c nonce).2.counter := by
  unfold step
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_refl _

/-- A previously accepted counter either remains marked or is too old.
This history invariant intentionally imposes no conditions on unseen bits. -/
def Remembers (c : ReplayCounter) (p : Nat) : Prop :=
  p + 1 ≤ c.counter ∧
  (c.counter ≤ p + 1 + 8128 → c.backtrack[slot (p + 1)]!.testBit (bit (p + 1)) = true)

/-- Every eligible call sets its own bit, whether or not it was fresh. -/
theorem update_remembers_self (c : ReplayCounter) (nonce : Nat)
    (hsize : c.backtrack.size = 128) : Remembers (update c nonce) nonce := by
  constructor
  · exact Nat.le_max_right _ _
  · intro _
    simp only [update]
    rw [Array.getElem!_set!_self]
    · exact testBit_set_self _ _
    · simp [slot, hsize, Nat.mod_lt _ (by decide : 0 < 128)]

/-- Updates retain the history invariant for every older accepted nonce. -/
theorem update_remembers (c : ReplayCounter) (nonce p : Nat)
    (hsize : c.backtrack.size = 128) (hp : Remembers c p) :
    Remembers (update c nonce) p := by
  constructor
  · exact Nat.le_trans hp.1 (Nat.le_max_left _ _)
  · intro hlive
    have hn : nonce + 1 ≤ p + 1 + 8128 := Nat.le_trans (Nat.le_max_right _ _) hlive
    have hc : c.counter ≤ p + 1 + 8128 := Nat.le_trans (Nat.le_max_left _ _) hlive
    have hold := hp.2 hc
    have hprep := prepared_get_live c (p + 1) (nonce + 1) hp.1 hn
    simp only [update]
    by_cases heq : slot (nonce + 1) = slot (p + 1)
    · rw [← heq, Array.getElem!_set!_self]
      · apply testBit_or_preserves
        simpa [heq, hprep] using hold
      · simp [slot, hsize, Nat.mod_lt _ (by decide : 0 < 128)]
    · rw [Array.getElem!_set!_ne _ _ _ _ heq, hprep]
      exact hold

/-- Once remembered, a nonce cannot be returned as fresh. -/
theorem remembered_rejected (c : ReplayCounter) (p : Nat) (hp : Remembers c p) :
    (step c p).1 = false := by
  unfold step
  split
  · rename_i h
    have hbit := hp.2 (by have := h.2.2; omega)
    simp [fresh, prepared, show ¬p + 1 > c.counter from Nat.not_lt.mpr hp.1, hbit]
  · rfl

/-- A successful result establishes the history invariant. -/
theorem accepted_remembered (c : ReplayCounter) (nonce : Nat)
    (hsize : c.backtrack.size = 128) (h : (step c nonce).1 = true) :
    Remembers (step c nonce).2 nonce := by
  by_cases he : eligible c nonce
  · rw [step, ite_eq_left he]
    exact update_remembers_self c nonce hsize
  · rw [step, ite_eq_right he] at h
    contradiction

/-- Each call preserves the remembered history. -/
theorem step_remembers (c : ReplayCounter) (nonce p : Nat)
    (hsize : c.backtrack.size = 128) (hp : Remembers c p) :
    Remembers (step c nonce).2 p := by
  unfold step
  split
  · exact update_remembers c nonce p hsize hp
  · exact hp

@[simp] theorem step_size (c : ReplayCounter) (nonce : Nat) :
    (step c nonce).2.backtrack.size = c.backtrack.size := by
  unfold step
  split <;> simp

/-- The successes selected from a finite list of pure calls. -/
def accepted (c : ReplayCounter) : List Nat → List Nat
  | [] => []
  | n :: ns =>
    let r := step c n
    let rest := accepted r.2 ns
    if r.1 then n :: rest else rest

theorem remembered_not_accepted (c : ReplayCounter) (p : Nat) (ns : List Nat)
    (hsize : c.backtrack.size = 128) (hp : Remembers c p) :
    p ∉ accepted c ns := by
  induction ns generalizing c with
  | nil => simp [accepted]
  | cons n ns ih =>
    have hs : (step c n).2.backtrack.size = 128 := by simpa using hsize
    have htail := ih (step c n).2 hs (step_remembers c n p hsize hp)
    cases hr : (step c n).1 with
    | false => simpa [accepted, hr] using htail
    | true =>
      have hne : p ≠ n := by
        intro heq
        subst n
        have hf := remembered_rejected c p hp
        simp [hr] at hf
      simp [accepted, hr, hne, htail]

/-- No nonce is accepted twice by any finite pure window execution, starting
from any shape-correct bitmap. This is the pure-model component of S1;
connecting the mirror and runner to these calls is a separate obligation. -/
theorem accepted_nodup (c : ReplayCounter) (ns : List Nat)
    (hsize : c.backtrack.size = 128) : (accepted c ns).Nodup := by
  induction ns generalizing c with
  | nil => simp [accepted]
  | cons n ns ih =>
    have hs : (step c n).2.backtrack.size = 128 := by simpa using hsize
    have htail := ih (step c n).2 hs
    cases hr : (step c n).1 with
    | false => simpa [accepted, hr] using htail
    | true =>
      have hnot := remembered_not_accepted (step c n).2 n ns hs
        (accepted_remembered c n hsize hr)
      simpa [accepted, hr] using List.nodup_cons.mpr ⟨hnot, htail⟩

end Leanux.Proofs.WG.CounterWindow
