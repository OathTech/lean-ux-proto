import Leanux.Proofs.WG.Roaming.Model
import Leanux.Proofs.WG.Noise.CryptoFrames

set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem endpointFromSkb_exact (src : SkbSource) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ endpointFromSkb src
    ⦃⇓? result w => ⌜P w.k ∧ result = some (sourceEndpoint src) ∧
      (src.family = 4 ∨ src.family = 6)⌝⦄ := by
  mvcgen [endpointFromSkb, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sourceEndpoint]

theorem endpointEq_destination (P : Kernel → Prop) (a : Endpoint) (b : Option Endpoint)
    (valid : a.family = AF_INET ∨ a.family = AF_INET6) :
    ⦃fun w => ⌜P w.k⌝⦄ endpointEq a b
    ⦃⇓? ok w => ⌜P w.k ∧ (ok = true → b.map destination = some (destination a))⌝⦄ := by
  mvcgen [endpointEq, Leanux.WG.andM, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals cases b <;> simp_all [destination, AF_INET, AF_INET6]
  all_goals grind

end Leanux.Proofs.WG.Roaming
