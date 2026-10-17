import Leanux.Proofs.WG.TimerDiscipline.JitterBoundSource

/-! Jitter is typed over WG.M, so preservation of WireGuard state remains a
substantive source property. Other product subsystems are excluded by its type. -/
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem jitter_wg_spec (P : WGWorld → Prop) (site : HiddenSite) :
    Ensures (jitterBelowRekeyTimeout site) P (fun _ g => P g) := by
  let step (_ : Nat) (_ : Option Nat × Unit) : WG.M (ForInStep (Option Nat × Unit)) := do
    let r := (← hidden site)[0]!.toNat
    if (HZ / 3 * r) % 256 ≥ 256 % (HZ / 3) then return .done (some (HZ / 3 * r / 256), ())
    return .yield (none, ())
  let finish (state : Option Nat × Unit) : WG.M Nat :=
    match state.1 with
    | some n => pure n
    | none => budgetExhausted "jitter draws"
  have hs (turn : Nat) (state : Option Nat × Unit) :
      Ensures (step turn state) P (fun _ g => P g) := by
    dsimp only [step]
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.hidden site) P)) ?_
    intro bytes g ambient result g' ambient' hp hr
    split at hr <;> cases hr <;> exact hp
  have hl (turns : List Nat) (state : Option Nat × Unit) :
      Ensures (forIn turns state step) P (fun _ g => P g) := by
    induction turns generalizing state with
    | nil =>
      intro g ambient result g' ambient' hp hr
      cases hr
      exact hp
    | cons turn turns ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (hs turn state) ?_
      intro out g ambient result g' ambient' hp hr
      cases out with
      | done s =>
        cases hr
        exact hp
      | yield s =>
        exact ih s g ambient result g' ambient' hp hr
  have factor : jitterBelowRekeyTimeout site = (do
      let budget ← (recordBudget : WG.M Nat)
      let state ← forIn ([:budget] : Std.Legacy.Range) (none, ()) step
      finish state) := by
    simp only [jitterBelowRekeyTimeout, finish, step]
    congr 1
    funext budget
    congr 1
    funext state
    cases state.1 <;> rfl
  rw [factor]
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant AmbientM.recordBudget P)) ?_
  intro budget
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine ensures_bind _ _ (hl _ (none, ())) ?_
  intro state
  cases hstate : state.1 with
  | none =>
    simp only [finish, hstate]
    exact (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.budgetExhausted "jitter draws") P)
  | some n =>
    intro g ambient result g' ambient' hp hr
    simp only [finish, hstate] at hr
    cases hr
    exact hp

end Leanux.Proofs.WG.TimerDiscipline
