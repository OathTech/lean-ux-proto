import Leanux.Proofs.WG.Noise.ConsumeEdges
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
    (invalid : ¬ validAllowedIp ip) (initial : Kernel) :
    Ensures (setAllowedip pid ip) (fun w => w.k = initial)
      (fun ret w => ret = -EINVAL ∧ w.k = initial) := by
  rw [ensures_iff]
  have hi := fun family addr cidr pid => unconstrained_prefix (insert family addr cidr pid)
  mvcgen [setAllowedip, Leanux.WG.orM, Leanux.WG.andM, branch, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [validAllowedIp, AF_INET, AF_INET6]
  all_goals cases hf : ip.family <;> cases ha : ip.addr <;> cases hc : ip.cidr <;>
    simp_all [validAllowedIp, AF_INET, AF_INET6]
  all_goals grind only

/-- A sufficient room bound for the complete allowed-IP attribute nest. -/
def allowedIpSpace (family : Nat) : Nat :=
  nlaTotal 0 + nlaTotal 1 + nlaTotal 2 + nlaTotal (if family = 6 then 16 else 4)

theorem getAllowedips_exact (skb : NlSkb) (family masked cidr : Nat)
    (room : allowedIpSpace family ≤ skb.room) (initial : Kernel) :
    Ensures (getAllowedips skb family masked cidr) (fun w => w.k = initial)
      (fun result w => w.k = initial ∧ result =
        ({ skb with room := skb.room - allowedIpSpace family },
          some (Lean.Json.mkObj [("family", Lean.toJson family),
            ("addr", Lean.toJson (hexBE masked (if family = 6 then 16 else 4))),
            ("cidr", Lean.toJson cidr)]))) := by
  rw [ensures_iff]
  mvcgen [getAllowedips, NlSkb.put, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [allowedIpSpace, nlaTotal]
  all_goals split at * <;> simp_all
  all_goals try assumption
  all_goals try simp_all [Nat.sub_sub]
  all_goals grind only

end Leanux.Proofs.WG.Config
