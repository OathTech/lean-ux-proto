import Leanux.Proofs.WG.Roaming.Model
import Leanux.Proofs.WG.Noise.CryptoFrames

set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem endpointFromSkb_exact (src : SkbSource) (P : WGWorld → Prop) :
    ⦃fun w => ⌜P w⌝⦄ endpointFromSkb src
    ⦃⇓? result w => ⌜P w ∧ result = some (sourceEndpoint src) ∧
      (src.family = 4 ∨ src.family = 6)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  by_cases v4 : src.family = 4
  · simp [endpointFromSkb, branch, AmbientM.branch, v4] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨pre, by simp [sourceEndpoint, v4], Or.inl v4⟩
  · by_cases v6 : src.family = 6
    · by_cases multicast : src.saddr / 2 ^ 120 = 0xff
      · simp [endpointFromSkb, branch, AmbientM.branch, v6, multicast,
          unsupported, AmbientM.unsupported] at run
        cases run
      · simp [endpointFromSkb, branch, AmbientM.branch, v6, multicast] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨pre, by simp [sourceEndpoint, v4], Or.inr v6⟩
    · simp [endpointFromSkb, branch, AmbientM.branch, v4, v6,
        invariant, AmbientM.invariant] at run
      cases run

theorem endpointEq_destination (P : WGWorld → Prop) (a : Endpoint) (b : Option Endpoint)
    (valid : a.family = AF_INET ∨ a.family = AF_INET6) :
    ⦃fun w => ⌜P w⌝⦄ endpointEq a b
    ⦃⇓? ok w => ⌜P w ∧ (ok = true → b.map destination = some (destination a))⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  rcases valid with v4 | v6
  all_goals cases b with
  | none =>
    simp [endpointEq, Leanux.WG.andM, branch, AmbientM.branch, AF_INET, AF_INET6,
      *] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨pre, by simp⟩
  | some b =>
    by_cases family : b.family = a.family <;>
      by_cases port : b.port = a.port <;>
      by_cases addr : b.addr = a.addr <;>
      by_cases src : b.src = a.src <;>
      by_cases srcIf : b.srcIf = a.srcIf <;>
      by_cases scope : b.scope = a.scope
    all_goals simp_all only [AF_INET, AF_INET6]
    all_goals simp [endpointEq, Leanux.WG.andM, branch, AmbientM.branch, AF_INET, AF_INET6, *] at run
    all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact ⟨pre, by simp_all [destination, AF_INET6]⟩

end Leanux.Proofs.WG.Roaming
