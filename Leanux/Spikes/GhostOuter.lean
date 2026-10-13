import Leanux.Spikes.GhostTools
import Init.Data.Array.Lemmas

/-! History erasure over a general base monad. This also covers the outer
runner's exception monad, whose World is an explicit loop variable. -/
namespace Leanux.Spikes.Ghost
open Leanux

def ErasesT {m : Type → Type} [Functor m] (g : StateT History m α) (o : m α) : Prop :=
  ∀ history, Prod.fst <$> g.run history = o

section Generic
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem erasesT_pure (a : α) : ErasesT (pure a : StateT History m α) (pure a) := by
  intro history
  simp only [StateT.run_pure, map_pure]

theorem erasesT_lift (o : m α) : ErasesT (StateT.lift o : StateT History m α) o := by
  intro history
  simp only [StateT.run_lift, map_bind, map_pure, bind_pure]

theorem erasesT_liftM (o : m α) : ErasesT (liftM o : StateT History m α) o :=
  erasesT_lift o

theorem erasesT_bind {g : StateT History m α} {o : m α}
    {gf : α → StateT History m β} {ofn : α → m β}
    (ha : ErasesT g o) (hb : ∀ a, ErasesT (gf a) (ofn a)) :
    ErasesT (g >>= gf) (o >>= ofn) := by
  intro history
  simp only [StateT.run_bind, map_bind]
  calc
    (g.run history >>= fun p => Prod.fst <$> (gf p.1).run p.2)
        = (g.run history >>= fun p => ofn p.1) := bind_congr (fun p => hb p.1 p.2)
    _ = (Prod.fst <$> g.run history) >>= ofn := (bind_map_left _ _ _).symm
    _ = o >>= ofn := by rw [ha history]

theorem erasesT_map {g : StateT History m α} {o : m α}
    (f : α → β) (h : ErasesT g o) : ErasesT (f <$> g) (f <$> o) := by
  simpa only [map_eq_pure_bind] using erasesT_bind h (fun a => erasesT_pure (f a))

omit [LawfulMonad m] in
theorem erasesT_ite (p : Prop) [Decidable p]
    {gt ge : StateT History m α} {ot oe : m α}
    (ht : p → ErasesT gt ot) (he : ¬ p → ErasesT ge oe) :
    ErasesT (if p then gt else ge) (if p then ot else oe) := by
  by_cases hp : p
  · simpa only [if_pos hp] using ht hp
  · simpa only [if_neg hp] using he hp

theorem erasesT_forIn (xs : List α) (b : β)
    (g : α → β → StateT History m (ForInStep β))
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
    (g : α → β → StateT History m (ForInStep β))
    (o : α → β → m (ForInStep β))
    (h : ∀ a b, ErasesT (g a b) (o a b)) :
    ErasesT (forIn xs b g) (forIn xs b o) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact erasesT_forIn _ b g o h

end Generic

theorem erasesT_throw (e : ε) :
    ErasesT (throw e : StateT History (Except ε) α) (throw e : Except ε α) := by
  intro history
  rfl

/-- Move the observer history outside one explicit World execution, attaching
exactly the runner's operation index to any original failure. -/
def runAtLogged (index : Nat) (world : World) (g : GhostM α) :
    StateT History (Except (Nat × Stop)) (α × World) := fun history =>
  (((g.run history).run world).map (fun ((a, h), w) => ((a, w), h))).mapError
    (fun e => (index, e))

theorem runAtLogged_erases (index : Nat) (world : World) (g : GhostM α) (o : M α)
    (h : Erases g o) :
    ErasesT (runAtLogged index world g) ((o.run world).mapError (fun e => (index, e))) := by
  intro history
  rw [← h history world]
  unfold runAtLogged
  cases he : (g.run history).run world with
  | error e => exact (congrArg (fun r => Prod.fst <$> (r.map (fun ((a, h), w) => ((a, w), h))).mapError (fun e => (index, e))) he).trans (by rfl)
  | ok out =>
    rcases out with ⟨⟨a, hist⟩, w⟩
    exact (congrArg (fun r => Prod.fst <$> (r.map (fun ((a, h), w) => ((a, w), h))).mapError (fun e => (index, e))) he).trans (by rfl)

/-- A successful original result has an observed result with exactly the same
value, and conversely. This does not assert any invariant of the history. -/
theorem erasesT_success_iff {g : StateT History (Except ε) α} {o : Except ε α}
    (h : ErasesT g o) (a : α) (history : History) :
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

end Leanux.Spikes.Ghost
