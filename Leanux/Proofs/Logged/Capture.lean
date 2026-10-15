import Leanux.Proofs.Logged.ProjectsUnder

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

/-- Execute the observer once, retaining its actual outgoing journal on both
success and failure. Only a successful return creates a witness. -/
def captureObserved (a : PrefixM Event α) : PrefixM Event (RunWitness α) :=
  fun w => ExceptT.mk fun h =>
    let out := runPrefix a w h
    (out.1.map (fun (x, v) => (⟨x, w, v⟩, v)), out.2)

theorem runPrefix_captureObserved (a : PrefixM Event α) (w : World) (h : List Event) :
    runPrefix (captureObserved a) w h =
      ((runPrefix a w h).1.map (fun (x, v) => (⟨x, w, v⟩, v)),
        (runPrefix a w h).2) := rfl

theorem Appends.captureObserved (ha : Appends a) : Appends (captureObserved a) := ha

theorem HistoryFrame.captureObserved (ha : HistoryFrame ρ a) :
    HistoryFrame ρ (captureObserved a) := ha

theorem PrefixPreserves.captureObserved (ha : PrefixPreserves I S a) :
    PrefixPreserves I S (captureObserved a) := by
  intro w h hi
  obtain ⟨s, he, hs, hn⟩ := ha w h hi
  refine ⟨s, he, hs, ?_⟩
  cases hr : (runPrefix a w h).1 with
  | error e => simp [runPrefix_captureObserved, hr, Except.map]
  | ok out => simpa [runPrefix_captureObserved, hr, Except.map] using hn

/-- Retain the actual incoming precondition and observer history in the
successful witness. The outgoing history here precedes any receipt emission;
on Stop it is exactly the underlying observer's outgoing history. -/
theorem PrefixEnsures.captureObserved (ha : PrefixEnsures P S a Q) :
    PrefixEnsures P S (captureObserved a)
      (fun r h v => r.after = v ∧ Q r.value h r.after ∧
        ∃ h0, P h0 r.before ∧
          runPrefix a r.before h0 = (.ok (r.value, r.after), h)) := by
  intro w h hi
  obtain ⟨s, hs, safe, normal⟩ := ha w h hi
  refine ⟨s, hs, safe, ?_⟩
  cases hr : runPrefix a w h with
  | mk result t =>
    cases result with
    | error e => simp [runPrefix_captureObserved, hr, Except.map]
    | ok out =>
      rcases out with ⟨x, v⟩
      simp only [hr] at normal
      simpa only [runPrefix_captureObserved, hr, Except.map] using
        (show v = v ∧ Q x t v ∧ ∃ h0, P h0 w ∧
          runPrefix a w h0 = (.ok (x, v), t) from ⟨rfl, normal, h, hi, hr⟩)

/-- Append a successful receipt without rerunning the action. -/
def receiptObserved (a : PrefixM Event α) (receipt : RunWitness α → Event) : PrefixM Event α := do
  let r ← captureObserved a
  emitPrefix (receipt r)
  return r.value

theorem runPrefix_receiptObserved (a : PrefixM Event α) (receipt : RunWitness α → Event)
    (w : World) (h : List Event) :
    runPrefix (receiptObserved a receipt) w h =
      match runPrefix a w h with
      | (.error e, t) => (.error e, t)
      | (.ok (x, v), t) => (.ok (x, v), t ++ [receipt ⟨x, w, v⟩]) := by
  rw [receiptObserved, runPrefix_bind, runPrefix_captureObserved]
  cases runPrefix a w h with
  | mk out t => cases out <;> rfl

theorem receiptObserved_projects (hr : ∀ r, ρ (receipt r) = none)
    (ha : ProjectsPrefix ρ id a b) : ProjectsPrefix ρ id (receiptObserved a receipt) b := by
  intro w h
  rw [ha w h, runPrefix_receiptObserved]
  cases runPrefix a w h with
  | mk out t => cases out <;> simp [List.filterMap_append, hr]

theorem receiptObserved_projectsUnder (hr : ∀ r, ρ (receipt r) = none)
    (ha : ProjectsUnder I ρ a b) : ProjectsUnder I ρ (receiptObserved a receipt) b := by
  intro w h hi
  rw [ha w h hi, runPrefix_receiptObserved]
  cases runPrefix a w h with
  | mk out t => cases out <;> simp [List.filterMap_append, hr]

theorem Appends.receiptObserved (ha : Appends a) : Appends (receiptObserved a receipt) :=
  ha.captureObserved.bind (fun _ =>
    (show Appends (emitPrefix _) from fun _ _ => ⟨[_], rfl⟩).bind (fun _ => Appends.pure _))

theorem HistoryFrame.receiptObserved (ha : HistoryFrame ρ a)
    (hr : ∀ r, ρ (receipt r) = none) : HistoryFrame ρ (receiptObserved a receipt) :=
  ha.captureObserved.bind (fun r => (HistoryFrame.emit _ (hr r)).bind (fun _ => HistoryFrame.pure _ _))

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
