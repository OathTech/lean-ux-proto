import Leanux.Proofs.WG.Progress.RecordSuffixModel
import Leanux.Proofs.Framing.Hoare

/-! Normal finite forIn executions reach a completion marker when every continuing turn consumes supplied records and the turn list is longer than the record list. This proof rule adds no operational loop and makes no callback-evaluation claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing

theorem forIn_record_budget_done {α β : Type}
    (step : α→β→Leanux.M (ForInStep β)) (Done : β→Prop)
    (turn : ∀ index state records,
      Hoare (step index state) (fun w=>w.ambient.hidden=some records)
        (fun result w=>match result with
          | .done value=>Done value
          | .yield _=>StrictTail records w.ambient.hidden))
    (indices : List α) (state : β) (records : List HiddenRecord)
    (before after : World) (result : β)
    (present : before.ambient.hidden=some records)
    (enough : records.length<indices.length)
    (run : (forIn indices state step).run before=.ok (result,after)) : Done result := by
  induction indices generalizing state records before after result with
  | nil => simp only [List.length_nil] at enough; omega
  | cons index indices ih =>
    rw [List.forIn_cons,StateT.run_bind] at run
    cases first : (step index state).run before with
    | error stop=>rw [first] at run; cases run
    | ok pair=>
      obtain ⟨out,middle⟩:=pair
      have post:=(hoare_iff_run _ _ _).mp (turn index state records)
        before out middle present first
      rw [first] at run
      cases out with
      | done value=>cases run; exact post
      | yield value=>
        obtain ⟨rest,remaining,_,shorter⟩:=post
        exact ih value rest middle after result remaining
          (by simp only [List.length_cons] at enough; omega) run

/-- When every actual yielded turn strictly decreases supplied records, any appended turns beyond a sufficiently long initial list are unreachable. The equality preserves all callback errors and final states; it makes no finite-evaluation claim. -/
theorem forIn_record_budget_append {α β : Type}
    (step : α→β→Leanux.M (ForInStep β))
    (strict : ∀ (index : α) (state next : β) (records : List HiddenRecord) (before after : World),
      before.ambient.hidden=some records →
      (step index state).run before=.ok (.yield next,after) →
      StrictTail records after.ambient.hidden)
    (indices extra : List α) (state : β) (records : List HiddenRecord)
    (before : World) (present : before.ambient.hidden=some records)
    (enough : records.length < indices.length) :
    (forIn (indices++extra) state step).run before=(forIn indices state step).run before := by
  induction indices generalizing state records before with
  | nil=>simp only [List.length_nil] at enough; omega
  | cons index indices ih=>
    simp only [List.cons_append,List.forIn_cons,StateT.run_bind]
    cases turn : (step index state).run before with
    | error stop=>rfl
    | ok pair=>
      obtain ⟨result,after⟩:=pair
      cases result with
      | done next=>rfl
      | yield next=>
        obtain ⟨rest,remaining,_,shorter⟩:=strict index state next records before after present turn
        exact ih next rest after remaining (by simp only [List.length_cons] at enough; omega)


end Leanux.Proofs.WG.Progress.RecordSuffix
