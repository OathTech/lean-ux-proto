import Leanux.Proofs.Logged.Prefix

/-! Failure-retaining observation for finite range loops and list mapping. -/

namespace Leanux.Proofs.Logged
open Leanux

/-- A finite list loop may carry an invariant of its changing accumulator,
while retaining the history safety condition on failures and early returns. -/
theorem PrefixEnsures.forInInvariant (xs : List α) (b : β)
    (g : α → β → PrefixM Event (ForInStep β))
    (I : β → List Event → World → Prop) (S : List Event → Prop)
    (hs : ∀ b h w, I b h w → S h)
    (hg : ∀ x b, PrefixEnsures (I b) S (g x b) (fun step => I step.value)) :
    PrefixEnsures (I b) S (forIn xs b g) I := by
  induction xs generalizing b with
  | nil =>
    simpa only [List.forIn_nil] using
      PrefixEnsures.pure (hs b) (fun _ _ hi => hi)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply PrefixEnsures.bind (hg x b)
    intro step
    cases step with
    | done b => exact PrefixEnsures.pure (hs b) (fun _ _ hi => hi)
    | yield b => exact ih b

/-- A finite range loop retains an accumulator-dependent invariant on either
normal exhaustion or early return, and history safety on every failure. -/
theorem PrefixEnsures.rangeInvariant (r : Std.Legacy.Range) (b : β)
    (g : Nat → β → PrefixM Event (ForInStep β))
    (I : β → List Event → World → Prop) (S : List Event → Prop)
    (hs : ∀ b h w, I b h w → S h)
    (hg : ∀ x b, PrefixEnsures (I b) S (g x b) (fun step => I step.value)) :
    PrefixEnsures (I b) S (forIn r b g) I := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact PrefixEnsures.forInInvariant _ b g I S hs hg

theorem erasesPrefix_range (r : Std.Legacy.Range) (b : β)
    (g : Nat → β → PrefixM Event (ForInStep β)) (a : Nat → β → M (ForInStep β))
    (ha : ∀ x b, ErasesPrefix (g x b) (a x b)) :
    ErasesPrefix (forIn r b g) (forIn r b a) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact erasesPrefix_forIn _ b g a ha

theorem PrefixPreserves.range (r : Std.Legacy.Range) (b : β)
    (g : Nat → β → PrefixM Event (ForInStep β))
    (hs : ∀ h w, I h w → S h) (hg : ∀ x b, PrefixPreserves I S (g x b)) :
    PrefixPreserves I S (ForIn.forIn r b g) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact PrefixPreserves.forIn _ b g hs hg

theorem erasesPrefix_mapM (xs : List α) (g : α → PrefixM Event β) (a : α → M β)
    (ha : ∀ x, ErasesPrefix (g x) (a x)) : ErasesPrefix (xs.mapM g) (xs.mapM a) := by
  induction xs with
  | nil => exact erasesPrefix_pure _
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact erasesPrefix_bind (ha x) (fun y => erasesPrefix_bind ih (fun ys => erasesPrefix_pure (y :: ys)))

theorem PrefixPreserves.mapM (xs : List α) (g : α → PrefixM Event β)
    (hs : ∀ h w, I h w → S h) (hg : ∀ x, PrefixPreserves I S (g x)) :
    PrefixPreserves I S (xs.mapM g) := by
  induction xs with
  | nil => exact PrefixPreserves.pure hs _
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact PrefixPreserves.bind (hg x) (fun y => PrefixPreserves.bind ih (fun ys => PrefixPreserves.pure hs (y :: ys)))

theorem erasesPrefix_forM (xs : List α) (g : α → PrefixM Event Unit) (a : α → M Unit)
    (ha : ∀ x, ErasesPrefix (g x) (a x)) : ErasesPrefix (xs.forM g) (xs.forM a) := by
  induction xs with
  | nil => simpa only [List.forM_eq_forM, List.forM_nil] using erasesPrefix_pure (Event := Event) ()
  | cons x xs ih =>
    simp only [List.forM_eq_forM, List.forM_cons] at *
    exact erasesPrefix_bind (ha x) (fun _ => ih)

theorem PrefixPreserves.forM (xs : List α) (g : α → PrefixM Event Unit)
    (hs : ∀ h w, I h w → S h) (hg : ∀ x, PrefixPreserves I S (g x)) :
    PrefixPreserves I S (xs.forM g) := by
  induction xs with
  | nil => simpa only [List.forM_eq_forM, List.forM_nil] using PrefixPreserves.pure hs ()
  | cons x xs ih =>
    simp only [List.forM_eq_forM, List.forM_cons] at *
    exact PrefixPreserves.bind (hg x) (fun _ => ih)

end Leanux.Proofs.Logged
