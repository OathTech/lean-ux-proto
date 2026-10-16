import Leanux.Proofs.WG.Noise.Basic

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Every ambient realization returns and establishes the native-state contract. -/
def Returns (a : StateT σ AmbientM α) (P : σ → Prop) (Q : α → σ → Prop) : Prop :=
  ∀ s ambient, P s → ∃ x s' ambient',
    (a.run s).run ambient = .ok ((x, s'), ambient') ∧ Q x s'

theorem returns_iff (a : StateT σ AmbientM α) (P : σ → Prop) (Q : α → σ → Prop) :
    Returns a P Q ↔ ⦃fun s => ⌜P s⌝⦄ a ⦃⇓ x s => ⌜Q x s⌝⦄ := by
  constructor
  · intro h s ambient hp
    obtain ⟨x, s', ambient', hr, hq⟩ := h s ambient hp
    dsimp only [StateT.run] at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hq
  · intro h s ambient hp
    have hh := h s ambient hp
    cases hr : (a.run s).run ambient with
    | error e =>
      dsimp only [StateT.run] at hr
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.false, ExceptConds.const, hr] at hh
    | ok out =>
      rcases out with ⟨⟨x, s'⟩, ambient'⟩
      refine ⟨x, s', ambient', rfl, ?_⟩
      dsimp only [StateT.run] at hr
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hh

theorem returns_bind (a : StateT σ AmbientM α) (f : α → StateT σ AmbientM β)
    (ha : Returns a P Q) (hf : ∀ x, Returns (f x) (Q x) R) :
    Returns (a >>= f) P R := by
  intro s ambient hp
  obtain ⟨x, s', ambient', hx, hq⟩ := ha s ambient hp
  obtain ⟨y, s'', ambient'', hy, hr⟩ := hf x s' ambient' hq
  refine ⟨y, s'', ambient'', ?_, hr⟩
  change ((a.run s).run ambient >>= fun ((v, t), b) => ((f v).run t).run b) = _
  rw [hx]
  exact hy

namespace Product

/-- Total correctness for every original product state and full-state predicate. -/
def Returns (a : StateT σ (Except Stop) α) (P : σ → Prop) (Q : α → σ → Prop) : Prop :=
  ∀ w, P w → ∃ x w', a.run w = .ok (x, w') ∧ Q x w'

theorem returns_iff (a : StateT σ (Except Stop) α) (P : σ → Prop) (Q : α → σ → Prop) :
    Returns a P Q ↔ ⦃fun w => ⌜P w⌝⦄ a ⦃⇓ x w => ⌜Q x w⌝⦄ := by
  constructor
  · intro h w hp
    obtain ⟨x, v, hr, hq⟩ := h w hp
    change a w = .ok (x, v) at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hq
  · intro h w hp
    have hh := h w hp
    cases hr : a w with
    | error e =>
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.false, ExceptConds.const, hr] at hh
    | ok out =>
      refine ⟨out.1, out.2, hr, ?_⟩
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hh

theorem returns_bind (a : StateT σ (Except Stop) α) (f : α → StateT σ (Except Stop) β)
    (ha : Returns a P Q) (hf : ∀ x, Returns (f x) (Q x) R) :
    Returns (a >>= f) P R := by
  intro w hp
  obtain ⟨x, v, hx, hq⟩ := ha w hp
  obtain ⟨y, u, hy, hr⟩ := hf x v hq
  refine ⟨y, u, ?_, hr⟩
  rw [StateT.run_bind, hx]
  exact hy

end Product
end Leanux.Proofs.WG.Config
