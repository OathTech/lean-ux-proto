import Leanux.Proofs.WG.CounterWindow.MirrorCalls

/-! Arithmetic bounds along finite executions of the receive window.
The stored high-water mark is one-based; the wire-counter lower edge is
inclusive. No subtraction is needed at the initially empty window. -/
namespace Leanux.Proofs.WG.CounterWindow
open Leanux Leanux.WG

/-- Every accepted wire counter lies inside the inclusive lower edge and
below the message-count limit. -/
theorem step_accepted_bounds (c : ReplayCounter) (nonce : Nat)
    (h : (step c nonce).1 = true) :
    c.counter ≤ nonce + 1 + COUNTER_WINDOW_SIZE ∧ nonce < REJECT_AFTER_MESSAGES := by
  have he := ((step_accepts_iff c nonce).mp h).1
  dsimp [COUNTER_WINDOW_SIZE]
  exact ⟨by have := he.2.2; omega, he.2.1⟩

/-- A wire counter strictly below the inclusive lower edge is rejected. -/
theorem step_below_rejected (c : ReplayCounter) (nonce : Nat)
    (h : nonce + 1 + COUNTER_WINDOW_SIZE < c.counter) :
    (step c nonce).1 = false := by
  cases hb : (step c nonce).1 with
  | false => rfl
  | true => have := (step_accepted_bounds c nonce hb).1; omega

/-- Every prefix retains the bitmap's shape. -/
theorem finish_size (c : ReplayCounter) (ns : List Nat) :
    (finish c ns).backtrack.size = c.backtrack.size := by
  induction ns generalizing c with
  | nil => rfl
  | cons n ns ih => simpa [finish] using ih (step c n).2

/-- The highest one-based counter cannot decrease along any finite run. -/
theorem finish_counter_mono (c : ReplayCounter) (ns : List Nat) :
    c.counter ≤ (finish c ns).counter := by
  induction ns generalizing c with
  | nil => exact Nat.le_refl _
  | cons n ns ih => exact Nat.le_trans (step_counter_mono c n) (ih (step c n).2)

/-- Every successful mirror validator call satisfies the arithmetic bounds. -/
theorem mirror_accepted_bounds (w w' : WGWorld) (ambient ambient' : Ambient) (kp : KeypairId)
    (c : ReplayCounter) (nonce : Nat) (hc : counterAt w kp = some c)
    (hs : c.backtrack.size = 128)
    (hr : ((counterValidate kp nonce).run w).run ambient = .ok ((true, w'), ambient')) :
    c.counter ≤ nonce + 1 + COUNTER_WINDOW_SIZE ∧ nonce < REJECT_AFTER_MESSAGES := by
  obtain ⟨out, outAmbient, he, _⟩ := mirror_step w ambient kp c nonce hc hs
  rw [hr] at he
  have hb : (step c nonce).1 = true := (congrArg (fun out => out.1.1) (Except.ok.inj he)).symm
  exact step_accepted_bounds c nonce hb

end Leanux.Proofs.WG.CounterWindow
