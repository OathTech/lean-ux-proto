import Leanux.Proofs.WG.Config.AllowedInsertSource
import Leanux.Proofs.WG.Config.DumpReturns

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem readInsertedNode (v4 : Bool) (addr cidr : Nat) (pid : PeerId)
    (parent : Slot) (P : WGWorld → Prop) :
    ⦃fun w => ⌜P w⌝⦄ readNode { newNode addr cidr (allowedBits v4) (some pid) with parent }
    ⦃⇓ result w => ⌜P w ∧ result = (allowedFamily v4, allowedMasked v4 addr cidr, cidr)⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient hp
  cases v4
  all_goals
    refine ⟨_, g, _, rfl, hp, ?_⟩
    simp [newNode, allowedBits, allowedFamily, allowedMasked]

theorem getAllowedips_inserted (v4 : Bool) (addr cidr : Nat) (skb : NlSkb)
    (room : allowedIpSpace (allowedFamily v4) ≤ skb.room) (P : WGWorld → Prop) :
    ⦃fun w => ⌜P w⌝⦄ getAllowedips skb (allowedFamily v4) (allowedMasked v4 addr cidr) cidr
    ⦃⇓ result w => ⌜P w ∧ result =
      ({ skb with room := skb.room - allowedIpSpace (allowedFamily v4) },
        some (allowedJson v4 addr cidr))⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient hp
  cases run : ((getAllowedips skb (allowedFamily v4) (allowedMasked v4 addr cidr) cidr).run g).run ambient with
  | error error =>
    have d : ¬ skb.room - 20 < (if v4 then 8 else 20) := by
      cases v4 <;> simp [allowedIpSpace, allowedFamily, nlaTotal] at room ⊢ <;> omega
    cases v4
    all_goals
      simp [allowedIpSpace, allowedFamily, nlaTotal] at room
      have a : ¬ skb.room < 4 := by omega
      have b : ¬ skb.room - 4 < 8 := by omega
      have c : ¬ skb.room - 12 < 8 := by omega
      dsimp at d
      simp [getAllowedips, NlSkb.put, nlaTotal, branch, AmbientM.branch,
        allowedFamily, a, b, c, d, Nat.sub_sub] at run
      cases run
  | ok out =>
    rcases out with ⟨⟨result, final⟩, after⟩
    have exactResult := getAllowedips_exact skb (allowedFamily v4)
      (allowedMasked v4 addr cidr) cidr room g g ambient result final after rfl run
    rcases exactResult with ⟨stateEq, resultEq⟩
    refine ⟨result, final, after, rfl, ?_, ?_⟩
    · simpa [stateEq] using hp
    · rw [resultEq]
      cases v4 <;> rfl

end Leanux.Proofs.WG.Config
