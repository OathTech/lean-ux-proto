import Leanux.Proofs.WG.TimerDiscipline.FireSelection
import Leanux.Proofs.WG.TimerDiscipline.InitiationFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Send-buffer allocation variant of Noise.keypairAllocation_kernel_spec. -/
theorem keypairAllocation_kernel_spec_sendBuffer_variant (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ hiddenAlloc .sendBufSkb
      ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hh := hidden_kernel_spec P
  noise_vcgen [hiddenAlloc, _private.Leanux.Kernel.Defs.«0».Leanux.allocRecord,
    _private.Leanux.Kernel.Defs.«0».Leanux.allocPlaceholder, invariant, unsupported, hh]
  case inv1 _ n _ _ _ _ _ _ => exact fun r _ => ⟨n - r.2 + 1⟩
  case inv2 => exact ((⇓? _ w => ⌜P w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try simp_all [WhileVariant.eval, SVal.evalsTo, SVal.uncurry, ExceptConds.true, ExceptConds.const]
  all_goals omega

/-- Kernel projection variant of the shared KernelFrames.skipCut_spec. -/
theorem skipCut_spec_kernel_variant (P : Kernel → Prop) (sites : List HiddenSite) :
    ⦃fun w => ⌜P w.k⌝⦄ skipCut sites ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hs : ⦃fun w => ⌜P w.k⌝⦄ skipCutSites sites
      ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
    mvcgen [skipCutSites, skipAmbient, noteNetRxStart, recordBudget, budgetExhausted, unsupported]
    case inv1 => exact ((⇓? _ w => ⌜P w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [ExceptConds.true, ExceptConds.const]
  have hm := map_result_spec (fun _ : List Nat => PUnit.unit) _ _ _ hs
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (ensures_iff _ _ _).mpr hm w result final pre run
  obtain ⟨_, _, post⟩ := h
  exact post

/-- Kernel projection variant of shared WGFrames.loopbackSend_spec. -/
theorem loopbackSend_spec_kernel_variant (P : Kernel → Prop) (sites : List HiddenSite) (raised : Bool) :
    ⦃fun w => ⌜P w.k⌝⦄ loopbackSend sites raised ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hc := skipCut_spec_kernel_variant P
  have hh := hidden_kernel_spec P
  mvcgen [loopbackSend, raiseLoopbackRx, loopbackSoftirq, peekHiddenSite, skipAmbient,
    getDev, getK, invariant, unsupported, hc, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.TimerDiscipline
