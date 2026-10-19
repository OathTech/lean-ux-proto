import SourceAdapter

/-! The allowed-IPs component's actual adapter, related to computations over World.
Device presence is the existing access precondition, not a new restriction on
entries, owner words, counts or input records. -/
namespace Binary.Source.Aip
open Leanux Leanux.WG

def store (d : Device) : AipStore := ⟨d.nodes, d.nextNode, d.peerAllowedips⟩

def install (w : World) (d : Device) (entries : AipStore) (ambient : Ambient) : World :=
  {w with wg := {w.wg with dev := some {d with nodes := entries.nodes, nextNode := entries.nextNode, peerAllowedips := entries.trie}}, ambient}

theorem install_current (w : World) (d : Device) (hd : w.wg.dev = some d) :
    install w d (store d) w.ambient = w := by
  cases w with
  | mk ambient tasks seccomp fs wg fixture =>
    cases wg
    cases hd
    rfl

def Corresponds (a : AipM α) (b : Leanux.M α) : Prop :=
  ∀ w d, w.wg.dev = some d → b.run w = do
    let ((v, entries), ambient) ← (a.run (store d)).run w.ambient
    pure (v, install w d entries ambient)

theorem pure_corr (v : α) : Corresponds (pure v) (pure v) := by
  intro w d hd
  simp only [StateT.run_pure, Source.except_pure, Source.except_ok_bind, install_current w d hd]

theorem bind_corr {a : AipM α} {b : Leanux.M α}
    {f : α → AipM β} {g : α → Leanux.M β}
    (ha : Corresponds a b) (hf : ∀ x, Corresponds (f x) (g x)) :
    Corresponds (a >>= f) (b >>= g) := by
  intro w d hd
  rw [StateT.run_bind, ha w d hd]
  cases h : (a.run (store d)).run w.ambient with
  | error e =>
    simp only [StateT.run] at h
    simp [StateT.run, bind, StateT.bind, h, Except.bind]
  | ok out =>
    rcases out with ⟨⟨v, entries⟩, ambient⟩
    simp only [Source.except_ok_bind, Source.except_pure]
    rw [hf v (install w d entries ambient) {d with nodes := entries.nodes, nextNode := entries.nextNode, peerAllowedips := entries.trie} rfl]
    simp only [StateT.run, bind, StateT.bind] at h ⊢
    rw [h]
    cases (f v entries ambient) <;> rfl

theorem native_corr (a : AipM α) : Corresponds a (liftWG (liftAip a)) := by
  intro w d hd
  simp only [StateT.run, liftWG, liftAip, WG.getDev, WG.modifyDev,
    bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get,
    StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    StateT.lift, liftM, monadLift, MonadLift.monadLift, Except.pure, Except.bind, hd, store]
  cases h : a (store d) w.ambient <;>
    simp only [store] at h <;> simp [hd, h, install]

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
    (f : α → β → AipM (ForInStep β)) (g : α → β → Leanux.M (ForInStep β))
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

end Binary.Source.Aip
