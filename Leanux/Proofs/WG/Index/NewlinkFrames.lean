import Leanux.Proofs.WG.Index.LifecycleModel
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.TimerDiscipline.SendCutFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Concrete within-WireGuard preservation support for newlink. The public
claims use the campaign snapshot; no unrelated subsystem is part of the invariant. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def TablesSafeKernel (k : Kernel) : Prop :=
  ∀ d, k.wg = some d → DeviceTablesSafe d

/-- Kernel projection variant of the shared skipCutExactly preservation
contract, reusing the existing campaign-2 skipCut variant. -/
theorem skipCutExactly_spec_kernel_variant (P : Kernel → Prop)
    (site : HiddenSite) (n : Nat) (between : List HiddenSite) :
    ⦃fun w => ⌜P w.k⌝⦄ skipCutExactly site n between
      ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hc := TimerDiscipline.skipCut_spec_kernel_variant P
  mvcgen [skipCutExactly, skipAmbient, noteNetRxStart, hc]
  case inv1 => exact ((⇓? _ w => ⌜P w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ExceptConds.true, ExceptConds.const]

theorem cookieCheckerInit_tables :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ cookieCheckerInit
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hh := hidden_kernel_spec TablesSafeKernel
  have ht := hiddenClock64_kernel_spec TablesSafeKernel
  mvcgen [cookieCheckerInit, modifyDev, modifyK, hh, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem pubkeyHashtableAlloc_tables :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ pubkeyHashtableAlloc
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hh := hidden_kernel_spec TablesSafeKernel
  mvcgen [pubkeyHashtableAlloc, envOk, modifyDev, modifyK, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem ratelimiterInit_tables :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ ratelimiterInit
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hh := hidden_kernel_spec TablesSafeKernel
  mvcgen [ratelimiterInit, envOk, branch, getK, modifyK, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel]

end Leanux.Proofs.WG.Index
