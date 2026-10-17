import Leanux.Proofs.WG.Noise.Execution
import Leanux.WG.Netlink
import Leanux.WG.NetlinkDump

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The configured netlink policy's complete accepted allowed-IP shape. -/
def validAllowedIp (ip : AllowedIpAttrs) : Prop :=
  ip.family.isSome ∧ ip.addr.isSome ∧ ip.cidr.isSome ∧
    ((ip.family = some AF_INET ∧ ip.cidr.getD 0 ≤ 32 ∧ ip.addrLen = 4) ∨
     (ip.family = some AF_INET6 ∧ ip.cidr.getD 0 ≤ 128 ∧ ip.addrLen = 16))

theorem setAllowedip_rejected (pid : PeerId) (ip : AllowedIpAttrs)
    (invalid : ¬ validAllowedIp ip) (initial : WGWorld) :
    Ensures (setAllowedip pid ip) (fun g => g = initial)
      (fun ret g => ret = -EINVAL ∧ g = initial) := by
  intro g ambient result final after state run
  cases hf : ip.family <;> cases ha : ip.addr <;> cases hc : ip.cidr
  all_goals try {
    simp [setAllowedip, WG.orM, WG.andM, branch, AmbientM.branch, hf, ha, hc] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, state⟩ }
  rename_i family addr cidr
  have no4 : ¬ (family = AF_INET ∧ cidr ≤ 32 ∧ ip.addrLen = 4) := by
    intro h
    apply invalid
    simp only [validAllowedIp, hf, ha, hc, Option.isSome_some, Option.getD_some,
      Option.some.injEq, true_and]
    exact Or.inl h
  have no6 : ¬ (family = AF_INET6 ∧ cidr ≤ 128 ∧ ip.addrLen = 16) := by
    intro h
    apply invalid
    simp only [validAllowedIp, hf, ha, hc, Option.isSome_some, Option.getD_some,
      Option.some.injEq, true_and]
    exact Or.inr h
  by_cases v4 : family = AF_INET <;> by_cases v6 : family = AF_INET6 <;>
    by_cases w4 : cidr ≤ 32 <;> by_cases w6 : cidr ≤ 128 <;>
    by_cases l4 : ip.addrLen = 4 <;> by_cases l6 : ip.addrLen = 16
  all_goals try { exfalso; apply no4; exact ⟨v4, w4, l4⟩ }
  all_goals try { exfalso; apply no6; exact ⟨v6, w6, l6⟩ }
  all_goals simp_all [setAllowedip, WG.orM, WG.andM, branch, AmbientM.branch]
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

/-- A sufficient room bound for the complete allowed-IP attribute nest. -/
def allowedIpSpace (family : Nat) : Nat :=
  nlaTotal 0 + nlaTotal 1 + nlaTotal 2 + nlaTotal (if family = 6 then 16 else 4)

theorem getAllowedips_exact (skb : NlSkb) (family masked cidr : Nat)
    (room : allowedIpSpace family ≤ skb.room) (initial : WGWorld) :
    Ensures (getAllowedips skb family masked cidr) (fun g => g = initial)
      (fun result g => g = initial ∧ result =
        ({ skb with room := skb.room - allowedIpSpace family },
          some (Lean.Json.mkObj [("family", Lean.toJson family),
            ("addr", Lean.toJson (hexBE masked (if family = 6 then 16 else 4))),
            ("cidr", Lean.toJson cidr)]))) := by
  intro g ambient result final after state run
  by_cases inet6 : family = 6
  all_goals simp [allowedIpSpace, nlaTotal, inet6] at room
  all_goals
    have a : ¬ skb.room < 4 := by omega
    have b : ¬ skb.room - 4 < 8 := by omega
    have c : ¬ skb.room - 12 < 8 := by omega
    have d : ¬ skb.room - 20 < (if family = 6 then 20 else 8) := by
      simp [inet6]; omega
    simp only [inet6, ↓reduceIte] at d
    simp [getAllowedips, NlSkb.put, nlaTotal, branch, AmbientM.branch, inet6,
      a, b, c, d, Nat.sub_sub] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨state, by simp [allowedIpSpace, nlaTotal, inet6]⟩

end Leanux.Proofs.WG.Config
