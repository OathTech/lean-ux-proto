import Leanux.Proofs.WG.Config.MultipartModel
import Leanux.Proofs.WG.Config.AllowedReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- Native companion used by native serializer compositions. -/
theorem getAllowedips_zero_native (skb : NlSkb) (family masked cidr : Nat)
    (room : skb.room = 0) (P : WGWorld → Prop) :
    ⦃fun g => ⌜P g⌝⦄ getAllowedips skb family masked cidr
    ⦃⇓ result g => ⌜P g ∧ result = (skb, none)⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  let after := {ambient with steps := ambient.steps.push {
    decision := Decision.getAipNoNest, outcome := true, netRx := ambient.netRxSection}}
  refine ⟨(skb, none), g, after, ?_, pre, rfl⟩
  simp [getAllowedips, NlSkb.put, room, nlaTotal, branch, AmbientM.branch]
  rfl

/-- The original arbitrary owner-state predicate, through the actual Product lift. -/
theorem getAllowedips_zero (skb : NlSkb) (family masked cidr : Nat)
    (room : skb.room = 0) (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Product.Returns (liftWG (getAllowedips skb family masked cidr))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun result w => P w.wg w.fs w.tasks w.seccomp ∧ result = (skb, none)) := by
  intro w pre
  obtain ⟨result, current, after, run, preserved, exactResult⟩ :=
    ((returns_iff _ _ _).mpr (getAllowedips_zero_native skb family masked cidr room
      (fun g => P g w.fs w.tasks w.seccomp))) w.wg w.ambient pre
  refine ⟨result, {w with wg := current, ambient := after}, ?_, preserved, exactResult⟩
  change (Except.bind (((getAllowedips skb family masked cidr).run w.wg).run w.ambient) _) = _
  rw [run]
  rfl

end Leanux.Proofs.WG.Config
