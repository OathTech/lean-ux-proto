import Leanux.Kernel.Defs
import Init.Data.Array.Lemmas

/-! Erasure of observer state over an arbitrary lawful base monad. -/
namespace Leanux.Proofs.Logged

def ErasesT {σ : Type} {m : Type → Type} [Functor m] (g : StateT σ m α) (o : m α) : Prop :=
  ∀ history, Prod.fst <$> g.run history = o

section Generic
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem erasesT_pure (a : α) : ErasesT (pure a : StateT σ m α) (pure a) := by
  intro history
  simp only [StateT.run_pure, map_pure]

theorem erasesT_lift (o : m α) : ErasesT (StateT.lift o : StateT σ m α) o := by
  intro history
  simp only [StateT.run_lift, map_bind, map_pure, bind_pure]

theorem erasesT_liftM (o : m α) : ErasesT (liftM o : StateT σ m α) o :=
  erasesT_lift o

theorem erasesT_bind {g : StateT σ m α} {o : m α}
    {gf : α → StateT σ m β} {ofn : α → m β}
    (ha : ErasesT g o) (hb : ∀ a, ErasesT (gf a) (ofn a)) :
    ErasesT (g >>= gf) (o >>= ofn) := by
  intro history
  simp only [StateT.run_bind, map_bind]
  calc
    (g.run history >>= fun p => Prod.fst <$> (gf p.1).run p.2)
        = (g.run history >>= fun p => ofn p.1) := bind_congr (fun p => hb p.1 p.2)
    _ = (Prod.fst <$> g.run history) >>= ofn := (bind_map_left _ _ _).symm
    _ = o >>= ofn := by rw [ha history]

theorem erasesT_map {g : StateT σ m α} {o : m α}
    (f : α → β) (h : ErasesT g o) : ErasesT (f <$> g) (f <$> o) := by
  simpa only [map_eq_pure_bind] using erasesT_bind h (fun a => erasesT_pure (f a))

omit [LawfulMonad m] in
theorem erasesT_ite (p : Prop) [Decidable p]
    {gt ge : StateT σ m α} {ot oe : m α}
    (ht : p → ErasesT gt ot) (he : ¬ p → ErasesT ge oe) :
    ErasesT (if p then gt else ge) (if p then ot else oe) := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using ht hp
  · simpa only [ite_eq_right hp] using he hp

theorem erasesT_forIn (xs : List α) (b : β)
    (g : α → β → StateT σ m (ForInStep β))
    (o : α → β → m (ForInStep β))
    (h : ∀ a b, ErasesT (g a b) (o a b)) :
    ErasesT (forIn xs b g) (forIn xs b o) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using erasesT_pure b
  | cons a xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply erasesT_bind (h a b)
    intro s
    cases s with
    | done b => exact erasesT_pure b
    | yield b => exact ih b

theorem erasesT_array (xs : Array α) (b : β)
    (g : α → β → StateT σ m (ForInStep β))
    (o : α → β → m (ForInStep β))
    (h : ∀ a b, ErasesT (g a b) (o a b)) :
    ErasesT (forIn xs b g) (forIn xs b o) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact erasesT_forIn _ b g o h

end Generic

theorem erasesT_throw (e : ε) :
    ErasesT (throw e : StateT σ (Except ε) α) (throw e : Except ε α) := by
  intro history
  rfl

/-- A successful original result has an observed result with exactly the same
value, and conversely. This does not assert any invariant of the history. -/
theorem erasesT_success_iff {g : StateT σ (Except ε) α} {o : Except ε α}
    (h : ErasesT g o) (a : α) (history : σ) :
    o = .ok a ↔ ∃ history', g.run history = .ok (a, history') := by
  have he := h history
  cases hg : g.run history with
  | error e =>
    rw [hg] at he
    change Except.error e = o at he
    constructor
    · intro ho
      have bad := he.trans ho
      cases bad
    · rintro ⟨hist, hr⟩
      cases hr
  | ok out =>
    rcases out with ⟨b, hist⟩
    rw [hg] at he
    change Except.ok b = o at he
    constructor
    · intro ho
      have hab : b = a := Except.ok.inj (he.trans ho)
      subst b
      exact ⟨hist, rfl⟩
    · rintro ⟨hist', hr⟩
      cases hr
      exact he.symm


end Leanux.Proofs.Logged
