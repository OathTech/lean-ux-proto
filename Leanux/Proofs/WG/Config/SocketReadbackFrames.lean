import Leanux.Proofs.WG.Config.SocketReadbackModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem getAllowedips_ipv4_short_native (skb : NlSkb) (masked cidr : Nat)
    (room : skb.room < 28) (P : WGWorld → Prop) :
    ⦃fun g => ⌜P g⌝⦄ getAllowedips skb 4 masked cidr
    ⦃⇓ result g => ⌜P g ∧ result = (skb, none)⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  by_cases nest : skb.room < 4
  · refine ⟨(skb, none), g, mark ambient .getAipNoNest true, ?_, pre, rfl⟩
    simp [getAllowedips, NlSkb.put, nlaTotal, nest, branch, AmbientM.branch, mark]
    rfl
  · let a0 := mark ambient .getAipNoNest false
    by_cases cidrRoom : skb.room - 4 < 8
    · refine ⟨(skb, none), g, mark a0 .getAipPutCidr true, ?_, pre, rfl⟩
      simp [getAllowedips, NlSkb.put, nlaTotal, nest, cidrRoom, branch, AmbientM.branch, a0, mark]
      rfl
    · let a1 := mark a0 .getAipPutCidr false
      by_cases familyRoom : skb.room - 12 < 8
      · refine ⟨(skb, none), g, mark a1 .getAipPutFamily true, ?_, pre, rfl⟩
        simp [getAllowedips, NlSkb.put, nlaTotal, nest, cidrRoom, familyRoom,
          Nat.sub_sub, branch, AmbientM.branch, a1, a0, mark]
        rfl
      · let a2 := mark a1 .getAipPutFamily false
        have addressRoom : skb.room - 20 < 8 := by omega
        refine ⟨(skb, none), g, mark (mark a2 .getAipFamily6 false) .getAipPutAddr true,
          ?_, pre, rfl⟩
        simp [getAllowedips, NlSkb.put, nlaTotal, nest, cidrRoom, familyRoom, addressRoom,
          Nat.sub_sub, branch, AmbientM.branch, a2, a1, a0, mark]
        rfl

/-- The old short-buffer frame retains every former owner predicate. -/
theorem getAllowedips_ipv4_short (skb : NlSkb) (masked cidr : Nat)
    (room : skb.room < 28) (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Product.Returns (liftWG (getAllowedips skb 4 masked cidr))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun result w => P w.wg w.fs w.tasks w.seccomp ∧ result = (skb, none)) := by
  intro w pre
  obtain ⟨result, current, after, run, preserved, exactResult⟩ :=
    ((returns_iff _ _ _).mpr (getAllowedips_ipv4_short_native skb masked cidr room
      (fun g => P g w.fs w.tasks w.seccomp))) w.wg w.ambient pre
  refine ⟨result, {w with wg := current, ambient := after}, ?_, preserved, exactResult⟩
  change (Except.bind (((getAllowedips skb 4 masked cidr).run w.wg).run w.ambient) _) = _
  rw [run]
  rfl

end Leanux.Proofs.WG.Config
