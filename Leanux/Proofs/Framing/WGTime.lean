import Leanux.Proofs.Framing.KernelEffects
import Leanux.WG.Handshake

/-! Original recorded age tests and timer jitter preserve the complete kernel. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem birthdateTest_sameKernel (birthday : Int64) (seconds : Nat) :
    SameKernel (birthdateTest birthday seconds) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (hiddenClock64_sameKernel .birthdateExpired) (fun k' => k' = k)
  mvcgen [birthdateTest, hs]

theorem birthdateHasExpired_sameKernel (birthday : Int64) (seconds : Nat) :
    SameKernel (birthdateHasExpired birthday seconds) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (birthdateTest_sameKernel birthday seconds) (fun k' => k' = k)
  mvcgen [birthdateHasExpired, hs]

theorem branchExpired_sameKernel (d : Decision) (birthday : Int64) (seconds : Nat)
    (f : Bool → Bool := id) : SameKernel (branchExpired d birthday seconds f) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (birthdateTest_sameKernel birthday seconds) (fun k' => k' = k)
  mvcgen [branchExpired, hs, branchCmp]

theorem jitterBelowRekeyTimeout_sameKernel (site : HiddenSite) :
    SameKernel (jitterBelowRekeyTimeout site) := by
  apply sameKernel_of_wp
  intro k
  have hh := sameKernel_wp _ (hidden_sameKernel site) (fun k' => k' = k)
  have hb := sameKernel_wp _ recordBudget_sameKernel (fun k' => k' = k)
  have he := sameKernel_wp _ (budgetExhausted_sameKernel (α := Nat) "jitter draws") (fun k' => k' = k)
  mvcgen [jitterBelowRekeyTimeout, hh, hb, he]
  all_goals try exact ((⇓? _ w => ⌜w.k = k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem callerJiffies_sameKernel (site : HiddenSite) : SameKernel (callerJiffies site) := by
  apply sameKernel_of_wp
  intro k
  have hh := sameKernel_wp _ (hiddenJiffies_sameKernel site) (fun k' => k' = k)
  mvcgen [callerJiffies, hh]

end Leanux.Proofs.Framing
