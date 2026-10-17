import Leanux.Proofs.WG.Campaign2.Bridge

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Campaign2.Product

/-- Inspect a source first on a copy, then execute the original operation. -/
def observed (a : M α) (probe : M β) : M (Outcome β × α) := do
  let observation ← Campaign2.Product.inspect probe
  let result ← a
  return (observation, result)

/-- Erasure retains every original success and exact error. -/
theorem observed_erase (a : M α) (probe : M β) :
    (do let result ← observed a probe; pure result.2) = a := by
  funext w
  change ((a.run w >>= fun out => Except.ok ((observeResult (probe.run w), out.1), out.2))
    >>= fun out => Except.ok (out.1.2, out.2)) = a.run w
  cases h : a.run w <;> rfl

theorem observed_effect (a : M α) (probe : M β) (P : Snapshot → Prop)
    (Q : (Outcome β × α) → Snapshot → Prop)
    (proof : ∀ w x final, P (snapshot w) → a.run w = .ok (x, final) →
      Q (observeResult (probe.run w), x) (snapshot final)) :
    Campaign2.Product.Ensures (observed a probe) P Q := by
  intro w result final pre run
  change (a.run w >>= fun out => Except.ok ((observeResult (probe.run w), out.1), out.2)) =
    .ok (result, final) at run
  cases h : a.run w with
  | error e => rw [h] at run; cases run
  | ok pair =>
    obtain ⟨x, after⟩ := pair
    rw [h] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact proof w x after pre h

theorem observe_ok {a : M α} {w final : World} {x : α}
    (run : a.run w = .ok (x, final)) :
    observeResult (a.run w) = .ok (x, snapshot final) := by rw [run]; rfl


end Leanux.Proofs.WG.TimerDiscipline
