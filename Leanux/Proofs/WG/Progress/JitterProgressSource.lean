import Leanux.Proofs.WG.Progress.JitterProgressModel
import Leanux.Proofs.WG.TimerDiscipline.JitterRecordsSource

/-! Exact correspondence to the original hidden read and record-budgeted
rejection loop. These are substantive operation equations, not frame lemmas. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.TimerDiscipline

theorem hidden_jitter_arbitrary (site : JitterSite) (w : World) (records : List HiddenRecord)
    (present : w.hidden = some records) :
    (hidden site.hiddenSite).run w =
      match resolveJitterInput site records with
      | .error error => .error error
      | .ok (bytes, rest) => .ok (bytes, {w with hidden := some rest}) := by
  cases site <;> cases stripped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil =>
    simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      present, HiddenSite.info, JitterSite.hiddenSite, Worker.sectionId, Worker.index, Except.pure, Except.bind,
      resolveJitterInput, stripped]
    rfl
  | cons record rest =>
    simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      present, HiddenSite.info, JitterSite.hiddenSite, Worker.sectionId, Worker.index, Except.pure, Except.bind,
      resolveJitterInput, stripped]
    split <;> (try rfl)
    split <;> rfl

theorem jitterStep_input (site : JitterSite) (turn : Nat) (state : Option Nat × Unit)
    (w : World) (records : List HiddenRecord) (present : w.hidden = some records) :
    (jitterStep site.hiddenSite turn state).run w =
      match resolveJitterInput site records with
      | .error error => .error error
      | .ok (bytes, rest) => .ok
        ((if jitterAccepted bytes[0]! then .done (some (jitterValue bytes[0]!), ())
          else .yield (none, ())), {w with hidden := some rest}) := by
  rw [jitterStep, StateT.run_bind, hidden_jitter_arbitrary site w records present]
  cases resolution : resolveJitterInput site records with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨bytes, rest⟩
    by_cases accepted : jitterAccepted bytes[0]!
    · simp only [ite_eq_left accepted]
      change ((if jitterAccepted bytes[0]! then _ else _) : M (ForInStep (Option Nat × Unit))).run _ = _
      rw [ite_eq_left accepted]
      rfl
    · simp only [ite_eq_right accepted]
      change ((if jitterAccepted bytes[0]! then _ else _) : M (ForInStep (Option Nat × Unit))).run _ = _
      rw [ite_eq_right accepted]
      rfl

theorem jitterLoop_input (site : JitterSite) (turns : List Nat) (records : List HiddenRecord)
    (enough : records.length + 1 ≤ turns.length) (w : World)
    (present : w.hidden = some records) :
    (jitterLoop site.hiddenSite turns).run w =
      match resolveJitterSearch site records with
      | .error error => .error error
      | .ok (jitter, rest) => .ok ((some jitter, ()), {w with hidden := some rest}) := by
  induction turns generalizing records w with
  | nil => simp at enough
  | cons turn turns ih =>
    rw [resolveJitterSearch]
    simp only [jitterLoop, List.forIn_cons, StateT.run_bind]
    rw [jitterStep_input site turn (none, ()) w records present]
    cases resolution : resolveJitterInput site records with
    | error error => rfl
    | ok pair =>
      rcases pair with ⟨bytes, rest⟩
      dsimp only
      by_cases accepted : jitterAccepted bytes[0]!
      · simp only [ite_eq_left accepted]
        rfl
      · simp only [ite_eq_right accepted]
        have smaller := (resolveJitterInput_suffix site records bytes rest resolution).2
        have bound : rest.length + 1 ≤ turns.length := by simp only [List.length_cons] at enough; omega
        have next := ih rest bound {w with hidden := some rest} rfl
        cases outcome : resolveJitterSearch site rest with
        | error error => simpa only [outcome, bind, Except.bind, jitterLoop] using next
        | ok pair =>
          rcases pair with ⟨jitter, tail⟩
          simpa only [outcome, bind, Except.bind, jitterLoop] using next

theorem jitter_input (site : JitterSite) (records : List HiddenRecord) (w : World)
    (present : w.hidden = some records) :
    (jitterBelowRekeyTimeout site.hiddenSite).run w =
      match resolveJitterSearch site records with
      | .error error => .error error
      | .ok (jitter, rest) => .ok (jitter, {w with hidden := some rest}) := by
  have budgetRun : recordBudget.run w = .ok (records.length + 1, w) := by
    change (Except.ok ((match w.hidden with | some rs => rs.length + 1 | none => DOMAIN_FILTER_TURNS), w)
      : Except Stop (Nat × World)) = _
    rw [present]
  have loop := jitterLoop_input site (List.range' 0 (records.length + 1)) records (by simp) w present
  have rangeEq :
      (forIn ([:records.length + 1] : Std.Legacy.Range) (none, ()) (jitterStep site.hiddenSite)) =
        jitterLoop site.hiddenSite (List.range' 0 (records.length + 1)) := by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', jitterLoop]
  rw [jitter_source, StateT.run_bind, budgetRun]
  change ((do
    let state ← forIn ([:records.length + 1] : Std.Legacy.Range) (none, ()) (jitterStep site.hiddenSite)
    jitterFinish state).run w) = _
  rw [StateT.run_bind, rangeEq, loop]
  cases outcome : resolveJitterSearch site records with
  | error error => rfl
  | ok pair => rcases pair with ⟨jitter, rest⟩; rfl
end Leanux.Proofs.WG.Progress
