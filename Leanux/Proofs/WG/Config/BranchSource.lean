import Leanux.Proofs.WG.Config.Returns

/-! Branch result contracts over any native outer state. Ambient inputs are
unrestricted; the return value and totality remain substantive after the state
split. These contracts do not specialize to the flat product monad. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem branch_state_spec {σ : Type} (P : σ → Prop)
    (decision : Decision) (outcome : Bool) :
    ⦃fun s => ⌜P s⌝⦄ (branch decision outcome : StateT σ AmbientM Bool)
    ⦃⇓? ret s => ⌜ret = outcome ∧ P s⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro s ambient ret s' ambient' hp hr
  change Except.ok ((outcome, s), {ambient with steps := ambient.steps.push {
    decision, outcome, netRx := ambient.netRxSection}}) = _ at hr
  cases hr
  exact ⟨rfl, hp⟩

theorem branch_state_returns {σ : Type} (P : σ → Prop)
    (decision : Decision) (outcome : Bool) :
    ⦃fun s => ⌜P s⌝⦄ (branch decision outcome : StateT σ AmbientM Bool)
    ⦃⇓ ret s => ⌜ret = outcome ∧ P s⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro s ambient hp
  exact ⟨outcome, s, {ambient with steps := ambient.steps.push {
    decision, outcome, netRx := ambient.netRxSection}}, rfl, rfl, hp⟩

end Leanux.Proofs.WG.Config
