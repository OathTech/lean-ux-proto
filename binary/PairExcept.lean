import PairMemory

namespace Binary.Pair

theorem bind_ok {x : Except ε α} {f : α → Except ε β} {result : β}
    (ok : (x >>= f) = .ok result) : ∃ value, x = .ok value ∧ f value = .ok result := by
  cases x with
  | error e => cases ok
  | ok value => exact ⟨value,rfl,ok⟩

theorem check_ok (p : Bool) (error : ε) (rest : Except ε α) (value : α)
    (ok : ((do
      unless p do throw error
      rest) : Except ε α) = .ok value) :
    p = true ∧ rest = .ok value := by
  cases p with
  | false => cases ok
  | true => exact ⟨rfl,ok⟩

theorem mapError_ok {x : Except ε α} {f : ε → ε'} {value : α}
    (ok : x.mapError f = .ok value) : x = .ok value := by
  cases x with
  | error e => cases ok
  | ok a => cases Except.ok.inj ok; rfl

inductive Mapped (R : α → β → Prop) : List α → List β → Prop
  | nil : Mapped R [] []
  | cons {x xs y ys} : R x y → Mapped R xs ys → Mapped R (x::xs) (y::ys)

theorem Mapped.imp {R S : α → β → Prop} {xs : List α} {ys : List β}
    (mapped : Mapped R xs ys) (imp : ∀ x y, R x y → S x y) : Mapped S xs ys := by
  induction mapped with
  | nil => exact .nil
  | cons head tail ih => exact .cons (imp _ _ head) ih

theorem Mapped.left {R : α → β → Prop} {xs : List α} {ys : List β}
    (mapped : Mapped R xs ys) (x : α) (member : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction mapped with
  | nil => cases member
  | @cons a as b bs head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨b,by simp,head⟩
    · obtain ⟨y,hy,rel⟩ := ih member
      exact ⟨y,by simp [hy],rel⟩

theorem Mapped.right {R : α → β → Prop} {xs : List α} {ys : List β}
    (mapped : Mapped R xs ys) (y : β) (member : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction mapped with
  | nil => cases member
  | @cons a as b bs head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨a,by simp,head⟩
    · obtain ⟨x,hx,rel⟩ := ih member
      exact ⟨x,by simp [hx],rel⟩

theorem mapM_ok {f : α → Except ε β} {xs : List α} {ys : List β}
    (ok : xs.mapM f = .ok ys) : Mapped (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ok; exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨y,head,ok⟩ := bind_ok ok
    obtain ⟨tail,rest,ok⟩ := bind_ok ok
    have eq : y :: tail = ys := Except.ok.inj ok
    subst ys
    exact .cons head (ih rest)

/-- A successful traversal visits every element when its body cannot return
`done`. The invariant extracted from a visit need not describe the accumulator. -/
theorem forIn_ok {f : α → σ → Except ε (ForInStep σ)} {xs : List α}
    {initial final : σ} {P : α → Prop}
    (step : ∀ x ∈ xs, ∀ before after, f x before = .ok after →
      ∃ next, after = .yield next ∧ P x)
    (ok : forIn xs initial f = .ok final) : ∀ x ∈ xs, P x := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
    rw [List.forIn_cons] at ok
    obtain ⟨after,head,ok⟩ := bind_ok ok
    obtain ⟨next,equal,property⟩ := step x (by simp) initial after head
    subst after
    have rest := ih (fun y hy => step y (by simp [hy])) ok
    intro y member
    rcases List.mem_cons.mp member with rfl | member
    · exact property
    · exact rest y member

theorem eraseDups_length_le [BEq α] (xs : List α) : xs.eraseDups.length ≤ xs.length := by
  cases xs with
  | nil => exact Nat.le_refl _
  | cons a xs =>
    rw [List.eraseDups_cons,List.length_cons,List.length_cons]
    have bound := eraseDups_length_le (xs.filter fun b => !b == a)
    have filtered := List.length_filter_le (fun b => !b == a) xs
    omega
termination_by xs.length
decreasing_by have := List.length_filter_le (fun b => !b == a) xs; simp; omega

theorem nodup_of_eraseDups_length [BEq α] [LawfulBEq α] (xs : List α)
    (length : xs.eraseDups.length = xs.length) : xs.Nodup := by
  cases xs with
  | nil => exact .nil
  | cons a xs =>
    rw [List.eraseDups_cons,List.length_cons,List.length_cons] at length
    have bound := eraseDups_length_le (xs.filter fun b => !b == a)
    have filtered := List.length_filter_le (fun b => !b == a) xs
    have equal : (xs.filter fun b => !b == a).length = xs.length := by omega
    have all := List.length_filter_eq_length_iff.mp equal
    have same : xs.filter (fun b => !b == a) = xs := List.filter_eq_self.mpr all
    rw [same] at length
    refine List.nodup_cons.mpr ⟨?_,nodup_of_eraseDups_length xs (by omega)⟩
    intro member
    simpa using all a member

end Binary.Pair
