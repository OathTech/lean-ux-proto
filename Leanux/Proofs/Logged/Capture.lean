import Leanux.Proofs.Logged.Prefix

/-! Exact original-action execution witnesses, retained only in proof-side
observations. Capturing an action changes neither its World nor its Stop. -/
namespace Leanux.Proofs.Logged
open Leanux

structure RunWitness (α : Type) where
  value : α
  before : World
  after : World

def RunWitness.Valid (a : M α) (r : RunWitness α) : Prop :=
  a.run r.before = .ok (r.value, r.after)

def captureRun (a : M α) : PrefixM Event (RunWitness α) :=
  fun w => ExceptT.mk fun h =>
    match a.run w with
    | .error e => (.error e, h)
    | .ok (x, v) => (.ok (⟨x, w, v⟩, v), h)

theorem runPrefix_captureRun (a : M α) (w : World) (h : List Event) :
    runPrefix (captureRun a) w h =
      match a.run w with
      | .error e => (.error e, h)
      | .ok (x, v) => (.ok (⟨x, w, v⟩, v), h) := rfl

theorem captureRun_bind_erases (a : M α) (g : RunWitness α → PrefixM Event β)
    (f : α → M β) (he : ∀ r, ErasesPrefix (g r) (f r.value)) :
    ErasesPrefix (captureRun a >>= g) (a >>= f) := by
  intro w h
  rw [runPrefix_bind]
  cases hr : a.run w with
  | error e => simp [runPrefix_captureRun, hr, StateT.run_bind]
  | ok result =>
    rcases result with ⟨x, v⟩
    simpa [runPrefix_captureRun, hr, StateT.run_bind] using he ⟨x, w, v⟩ v h

theorem emitThen_erases (e : Event) (a : M α) :
    ErasesPrefix (do emitPrefix e; liftPrefix a) a := by
  intro w h
  simp [runPrefix_bind]

/-- Capture the exact successful run without changing its result or history.
Failure retains the previous history and exact original Stop. -/
theorem PrefixEnsures.captureRun (a : M α)
    (hs : ∀ h w, P h w → S h)
    (hq : ∀ h w x v, P h w → a.run w = .ok (x, v) → Q ⟨x, w, v⟩ h v) :
    PrefixEnsures P S (captureRun a) Q := by
  intro w h hi
  cases hr : a.run w with
  | error e =>
    exact ⟨[], by simp [runPrefix_captureRun, hr],
      by simpa [runPrefix_captureRun, hr] using hs h w hi,
      by simp [runPrefix_captureRun, hr]⟩
  | ok result =>
    rcases result with ⟨x, v⟩
    exact ⟨[], by simp [runPrefix_captureRun, hr],
      by simpa [runPrefix_captureRun, hr] using hs h w hi,
      by simpa [runPrefix_captureRun, hr] using hq h w x v hi hr⟩

end Leanux.Proofs.Logged
