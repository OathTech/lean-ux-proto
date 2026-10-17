import Leanux.Proofs.WG.Noise.ComponentFrames
import Leanux.WG.Handshake

/-! The timer jitter's numeric bound, independently of its state-preservation
contract in JitterFrames. Normal return is the only execution premise. -/
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem jitter_bounded (site : HiddenSite) :
    Ensures (jitterBelowRekeyTimeout site) (fun _ => True) (fun n _ => n < HZ / 3) := by
  let P : WGWorld → Prop := fun _ => True
  have effect : Ensures (jitterBelowRekeyTimeout site) P (fun n g => P g ∧ n < HZ / 3) := by
    let step (_ : Nat) (_ : Option Nat × Unit) : WG.M (ForInStep (Option Nat × Unit)) := do
      let r := (← hidden site)[0]!.toNat
      if (HZ / 3 * r) % 256 ≥ 256 % (HZ / 3) then return .done (some (HZ / 3 * r / 256), ())
      return .yield (none, ())
    let finish (state : Option Nat × Unit) : WG.M Nat :=
      match state.1 with
      | some n => pure n
      | none => budgetExhausted "jitter draws"
    let B (state : Option Nat × Unit) : Prop := ∀ n, state.1 = some n → n < HZ / 3
    have byte_bound (byte : UInt8) : HZ / 3 * byte.toNat / 256 < HZ / 3 := by
      have hb := UInt8.toNat_lt_size byte
      change _ < 256 at hb
      change 83 * byte.toNat / 256 < 83
      omega
    have hs (turn : Nat) (state : Option Nat × Unit) :
        Ensures (step turn state) P
          (fun result g => P g ∧ match result with | .done s | .yield s => B s) := by
      dsimp only [step]
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.hidden site) P)) ?_
      intro bytes g ambient result g' ambient' hp hr
      split at hr
      · cases hr
        refine ⟨hp, ?_⟩
        intro n eq
        cases eq
        exact byte_bound _
      · cases hr
        exact ⟨hp, by intro n eq; cases eq⟩
    have hl (turns : List Nat) (state : Option Nat × Unit) (bounded : B state) :
        Ensures (forIn turns state step) P (fun out g => P g ∧ B out) := by
      induction turns generalizing state with
      | nil =>
        intro g ambient result g' ambient' hp hr
        cases hr
        exact ⟨hp, bounded⟩
      | cons turn turns ih =>
        rw [List.forIn_cons]
        refine ensures_bind _ _ (hs turn state) ?_
        intro out g ambient result g' ambient' hp hr
        cases out with
        | done s =>
          cases hr
          exact hp
        | yield s =>
          exact ih s hp.2 g ambient result g' ambient' hp.1 hr
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
    refine ensures_bind _ _ (hl _ (none, ()) (by intro n eq; cases eq)) ?_
    intro state g ambient result g' ambient' hp hr
    cases hstate : state.1 with
    | none =>
      cases hh : ambient.hidden <;>
        simp [finish, hstate, budgetExhausted, AmbientM.budgetExhausted, hh,
          AmbientM.invariant, AmbientM.unsupported] at hr
      all_goals cases hr
    | some n =>
      simp only [finish, hstate] at hr
      cases hr
      exact ⟨hp.1, hp.2 _ hstate⟩
  intro g ambient n g' ambient' _ hr
  exact (effect g ambient n g' ambient' trivial hr).2

end Leanux.Proofs.WG.TimerDiscipline
