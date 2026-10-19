import Leanux.Proofs.WG.Progress.DeferredFiniteOuterSource
import Leanux.Proofs.WG.Campaign2.Bridge
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DeferredFinite
open Leanux Leanux.WG
/-- Exact finite original timers evaluation, preserving every native Stop. -/
theorem original_timers_finite (j : UInt64) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.runTimers j) (nativeTimers j) := by
  rw [nativeTimers_source j]
  intro state pre
  rfl

/-- Exact finite original placeholder evaluation, preserving every native Stop. -/
theorem original_placeholder_finite (j : UInt64) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.runTimersPlaceholder j) (nativePlaceholder j) := by
  rw [nativePlaceholder_source j]
  intro state pre
  rfl

/-- Exact finite original afterXmit evaluation, preserving every native Stop. -/
theorem original_afterXmit_finite  :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.afterXmit) (nativeAfterXmit ) := by
  rw [nativeAfterXmit_source ]
  intro state pre
  rfl

/-- Exact finite original idle evaluation, preserving every native Stop. -/
theorem original_idle_finite  :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.idleTimers) (nativeIdle ) := by
  rw [nativeIdle_source ]
  intro state pre
  rfl

/-- Exact finite original afterAdvance evaluation, preserving every native Stop. -/
theorem original_afterAdvance_finite  :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.afterAdvance) (nativeAfterAdvance ) := by
  rw [nativeAfterAdvance_source ]
  intro state pre
  rfl

end Leanux.Proofs.WG.Progress.DeferredFinite
