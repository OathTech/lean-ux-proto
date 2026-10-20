import MirrorHistory

namespace Binary.MirrorHistory
open Leanux

/-- Erasure at an entry state, for adapters with a source-level access guard. -/
def ErasesAt (logged : Logged α) (original : Leanux.M α) (w : World) : Prop :=
  ∀ history, erase ((logged.run history).run w) = original.run w

theorem Erases.at {logged : Logged α} {original : Leanux.M α}
    (h : Erases logged original) (w : World) : ErasesAt logged original w :=
  fun history => h history w

theorem erases_bind_at {logged : Logged α} {original : Leanux.M α}
    {lg : α → Logged β} {og : α → Leanux.M β} {w : World}
    (ha : ErasesAt logged original w)
    (hb : ∀ a next, original.run w = .ok (a,next) → ErasesAt (lg a) (og a) next) :
    ErasesAt (logged >>= lg) (original >>= og) w := by
  intro history
  simp only [StateT.run_bind]
  have hm := ha history
  cases he : (logged.run history).run w with
  | error e =>
    simp only [he, erase] at hm
    simp [← hm, erase]
    rfl
  | ok out =>
    rcases out with ⟨⟨a,h⟩,next⟩
    simp only [he, erase] at hm
    simpa [← hm, erase] using hb a next hm.symm h

theorem called_erases_at (symbol : String) {logged : Logged α} {original : Leanux.M α}
    {w : World} (h : ErasesAt logged original w) : ErasesAt (called symbol logged) original w := by
  intro history
  have erased := h (history ++ [⟨.call symbol,w⟩])
  rw [← erased]
  cases run : (logged.run (history ++ [⟨.call symbol,w⟩])).run w <;>
    simp [called, mark, StateT.run_bind, run, erase] <;> rfl

end Binary.MirrorHistory
