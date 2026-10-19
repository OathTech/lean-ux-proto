import Leanux.Proofs.WG.Progress.SchedulerRecordSource
import Leanux.Proofs.WG.Progress.RecordBudgetSource

/-! The original scheduler's supplied-record budget is adequate for its own loop. This excludes reaching that loop's exhaustion continuation after normal turns; every callback Stop remains unchanged. No finite-evaluation, activation-occupancy or global-completion claim is made. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged

/-- Only the two return markers present in the unchanged source can be returned. The trivial intermediate contracts classify results; they make no evaluation claim. -/
theorem scheduleTurn_result (stack : Option Worker) :
    Hoare (scheduleTurn stack) (fun _=>True)
      (fun result _=>result=turnReturn ∨ result=turnContinue) := by
  have any {α : Type} (action : Leanux.M α) : Hoare action (fun _=>True) (fun _ _=>True) := by
    apply (hoare_iff_run _ _ _).mpr
    intro _ _ _ _ _
    trivial
  have finish (value : TurnResult) (shape : value=turnReturn ∨ value=turnContinue) :
      Hoare (pure value : Leanux.M TurnResult) (fun _=>True)
        (fun result _=>result=turnReturn ∨ result=turnContinue) := by
    exact hoare_consequence (hoare_pure value (fun _=>True)) (fun _ h=>h)
      (fun _ _ h=>h.1 ▸ shape)
  have stop {α : Type} (message : String) (Q : α→World→Prop) :
      Hoare (invariant message : Leanux.M α) (fun _=>True) Q := by
    apply (hoare_iff_run _ _ _).mpr
    intro before result after pre run
    cases run
  have unsupportedStop {α : Type} (message : String) (Q : α→World→Prop) :
      Hoare (unsupported message : Leanux.M α) (fun _=>True) Q := by
    apply (hoare_iff_run _ _ _).mpr
    intro before result after pre run
    cases run
  unfold scheduleTurn scheduleTurnWith resumeCandidatesWith
  dsimp only
  repeat' first
    | with_reducible exact finish turnReturn (Or.inl rfl)
    | with_reducible exact finish turnContinue (Or.inr rfl)
    | with_reducible exact stop _ _
    | with_reducible exact unsupportedStop _ _
    | with_reducible apply hoare_bind _ _ (any _)
    | split
    | (with_reducible intro x; try dsimp only)

/-- A normal execution of the actual loop exits through its done marker when its captured turn list is longer than the supplied record list. The induction uses concrete strict continuing-turn effects. -/
theorem scheduleLoop_normal_done (stack : Option Worker)
    (turns : List Nat) (records : List HiddenRecord)
    (before after : World) (result : Option Unit × Unit)
    (present : before.ambient.hidden=some records)
    (enough : records.length < turns.length)
    (run : (forIn turns ((none,()) : Option Unit × Unit)
      (fun _ _=>scheduleTurn stack)).run before=.ok (result,after)) :
    result=(some (),()) := by
  apply forIn_record_budget_done (fun (_ : Nat) (_ : Option Unit×Unit)=>scheduleTurn stack)
    (fun value=>value=(some (),())) ?_ turns (none,()) records before after result present enough run
  intro index state input
  apply (hoare_iff_run _ _ _).mpr
  intro entry out final stored executed
  have shape:=(hoare_iff_run _ _ _).mp (scheduleTurn_result stack) entry out final trivial executed
  rcases shape with rfl | rfl
  · rfl
  · exact scheduleTurn_continue_strict stack input entry final stored executed

/-- Exact original outcome and final World with only the unreachable outer exhaustion continuation removed. The body is the existing forIn factor, not a new evaluator; inner Stops are propagated unchanged. -/
theorem schedule_supplied_source (stack : Option Worker) (records : List HiddenRecord)
    (before : World) (present : before.ambient.hidden=some records) :
    (Env.schedule stack).run before =
      ((do
        let _ ← forIn (List.range' 0 (records.length+1)) ((none,()) : Option Unit × Unit)
          (fun _ _=>scheduleTurn stack)
        pure () : Leanux.M Unit).run before) := by
  have budget : (recordBudget : Leanux.M Nat).run before=.ok (records.length+1,before) := by
    change Except.ok ((match before.ambient.hidden with
      | some rs=>rs.length+1
      | none=>DOMAIN_FILTER_TURNS),before)=_
    rw [present]
  rw [schedule_source,StateT.run_bind,budget]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (((forIn (List.range' 0 (records.length+1)) ((none,()) : Option Unit × Unit)
    (fun _ _=>scheduleTurn stack)).run before) >>= _) = _
  rw [StateT.run_bind]
  cases loop : (forIn (List.range' 0 (records.length+1)) ((none,()) : Option Unit × Unit)
      (fun _ _=>scheduleTurn stack)).run before with
  | error stop => rfl
  | ok pair =>
    obtain ⟨result,after⟩:=pair
    have done:=scheduleLoop_normal_done stack (List.range' 0 (records.length+1))
      records before after result present (by simp only [List.length_range']; omega) loop
    subst result
    rfl


end Leanux.Proofs.WG.Progress.RecordSuffix
