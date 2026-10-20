import PairExcept

namespace Binary.Pair

theorem forIn_identity {xs : List α} {f : α → σ → Except ε (ForInStep σ)}
    (unchanged : ∀ x ∈ xs, ∀ state, f x state=.ok (.yield state)) (initial : σ) :
    forIn xs initial f=.ok initial := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons,unchanged x (by simp) initial]
    exact ih (fun y hy => unchanged y (by simp [hy]))

theorem forIn_append_identity {xs ys : List α} {f : α → σ → Except ε (ForInStep σ)}
    (unchanged : ∀ x ∈ ys, ∀ state, f x state=.ok (.yield state)) (initial : σ) :
    forIn (xs++ys) initial f=forIn xs initial f := by
  induction xs generalizing initial with
  | nil => exact forIn_identity unchanged initial
  | cons x xs ih =>
    simp only [List.cons_append,List.forIn_cons]
    congr 1
    funext step
    cases step with
    | done value => rfl
    | yield value => exact ih value

/-- Loop bodies need agree only on elements the traversal actually visits. -/
theorem forIn_congr_mem {xs : List α} {f g : α → σ → Except ε (ForInStep σ)}
    (same : ∀ x ∈ xs, ∀ state, f x state=g x state) (initial : σ) :
    forIn xs initial f=forIn xs initial g := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    rw [same x (by simp) initial]
    congr 1
    funext step
    cases step with
    | done value => rfl
    | yield value => exact ih (fun y hy => same y (by simp [hy])) value

/-- A successful non-breaking traversal can be followed by a new suffix. -/
theorem forIn_append_yield {xs ys : List α} {f : α → σ → Except ε (ForInStep σ)}
    (yields : ∀ x ∈ xs, ∀ before after, f x before=.ok after → ∃ next, after=.yield next)
    {initial final : σ} (run : forIn xs initial f=.ok final) :
    forIn (xs++ys) initial f=forIn ys final f := by
  induction xs generalizing initial with
  | nil => cases Except.ok.inj run; rfl
  | cons x xs ih =>
    rw [List.forIn_cons] at run
    obtain ⟨after,first,run⟩ := bind_ok run
    obtain ⟨next,rfl⟩ := yields x (by simp) initial after first
    simp only [List.cons_append,List.forIn_cons,first]
    exact ih (fun y hy => yields y (by simp [hy])) run

end Binary.Pair
