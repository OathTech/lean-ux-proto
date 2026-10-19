import SourceAdapter

/-! The index component's actual adapter, related to computations over World.
Device presence is the existing access precondition, not a new restriction on
entries, owner words, counts or input records. -/
namespace Binary.Source.Index
open Leanux Leanux.WG

def install (w : World) (d : Device) (entries : List IndexEntry) (ambient : Ambient) : World :=
  {w with wg := {w.wg with dev := some {d with indexTable := entries}}, ambient}

theorem install_current (w : World) (d : Device) (hd : w.wg.dev = some d) :
    install w d d.indexTable w.ambient = w := by
  cases w with
  | mk ambient tasks seccomp fs wg fixture =>
    cases wg
    cases hd
    rfl

def Corresponds (a : IndexM α) (b : Leanux.M α) : Prop :=
  ∀ w d, w.wg.dev = some d → b.run w = do
    let ((v, entries), ambient) ← (a.run d.indexTable).run w.ambient
    pure (v, install w d entries ambient)

theorem pure_corr (v : α) : Corresponds (pure v) (pure v) := by
  intro w d hd
  simp only [StateT.run_pure, Source.except_pure, Source.except_ok_bind, install_current w d hd]

theorem bind_corr {a : IndexM α} {b : Leanux.M α}
    {f : α → IndexM β} {g : α → Leanux.M β}
    (ha : Corresponds a b) (hf : ∀ x, Corresponds (f x) (g x)) :
    Corresponds (a >>= f) (b >>= g) := by
  intro w d hd
  rw [StateT.run_bind, ha w d hd]
  cases h : (a.run d.indexTable).run w.ambient with
  | error e =>
    simp only [StateT.run] at h
    simp [StateT.run, bind, StateT.bind, h, Except.bind]
  | ok out =>
    rcases out with ⟨⟨v, entries⟩, ambient⟩
    simp only [Source.except_ok_bind, Source.except_pure]
    rw [hf v (install w d entries ambient) {d with indexTable := entries} rfl]
    simp only [StateT.run, bind, StateT.bind] at h ⊢
    rw [h]
    cases (f v entries ambient) <;> rfl

theorem native_corr (a : IndexM α) : Corresponds a (liftWG (liftIndex a)) := by
  intro w d hd
  simp only [StateT.run, liftWG, liftIndex, WG.getDev, WG.modifyDev,
    bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get,
    StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    StateT.lift, liftM, monadLift, MonadLift.monadLift, Except.pure, Except.bind, hd]
  cases a d.indexTable w.ambient <;> simp [hd, install]

theorem get_corr : Corresponds (get : IndexM (List IndexEntry))
    (do return (← Source.getDev).indexTable) := by
  intro w d hd
  simp only [Source.getDev, StateT.run, liftWG, WG.getDev,
    bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get,
    StateT.get, Except.pure, Except.bind, hd]
  rw [install_current w d hd]

theorem modify_corr (f : List IndexEntry → List IndexEntry) :
    Corresponds (modify f) (Source.modifyDev fun d => {d with indexTable := f d.indexTable}) := by
  intro w d hd
  simp [Source.modifyDev, liftWG, WG.modifyDev, StateT.run, bind,
    pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    Except.pure, Except.bind, hd, install]

theorem ambient_corr (a : AmbientM α) :
    Corresponds (StateT.lift a) (liftAmbient a) := by
  intro w d hd
  cases w with
  | mk ambient tasks seccomp fs wg fixture =>
    cases wg
    cases hd
    simp only [StateT.run, StateT.lift, liftAmbient, bind, StateT.bind]
    cases a ambient <;> rfl


theorem forIn_corr (xs : List α) (initial : β)
    (f : α → β → IndexM (ForInStep β)) (g : α → β → Leanux.M (ForInStep β))
    (h : ∀ x b, Corresponds (f x b) (g x b)) :
    Corresponds (forIn xs initial f) (forIn xs initial g) := by
  induction xs generalizing initial with
  | nil => exact pure_corr initial
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply bind_corr (h x initial)
    intro step
    cases step with
    | done value => exact pure_corr value
    | yield value => exact ih value

end Binary.Source.Index
