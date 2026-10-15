import Leanux.Proofs.WG.Noise.Basic

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The operation returns normally and establishes its result contract. -/
def Returns (a : M α) (P : World → Prop) (Q : α → World → Prop) : Prop :=
  ∀ w, P w → ∃ x w', a.run w = .ok (x, w') ∧ Q x w'

theorem returns_iff (a : M α) (P : World → Prop) (Q : α → World → Prop) :
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
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hh
    | ok out =>
      refine ⟨out.1, out.2, hr, ?_⟩
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hh

theorem returns_bind (a : M α) (f : α → M β)
    (ha : Returns a P Q) (hf : ∀ x, Returns (f x) (Q x) R) :
    Returns (a >>= f) P R := by
  intro w hp
  obtain ⟨x, v, hx, hq⟩ := ha w hp
  obtain ⟨y, u, hy, hr⟩ := hf x v hq
  refine ⟨y, u, ?_, hr⟩
  rw [StateT.run_bind, hx]
  exact hy

end Leanux.Proofs.WG.Config
