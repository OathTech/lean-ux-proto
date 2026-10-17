import Leanux.Proofs.WG.Config.SuffixReadbackModel
import Leanux.Proofs.WG.Config.MultipartLeaves

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem readNode_ipv4_native (n : AipNode) (width : n.bitlen = 32) (P : WGWorld → Prop) :
    ⦃fun g => ⌜P g⌝⦄ readNode n
    ⦃⇓ result g => ⌜P g ∧ result = (4, allowedMasked true n.bits n.cidr, n.cidr)⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let after := mark (mark ambient .swapEndian32 true) .readNodeHasCidr (n.cidr != 0)
  refine ⟨_, g, after, ?_, pre, rfl⟩
  by_cases zero : n.cidr = 0
  all_goals simp [readNode, swapEndian, width, branch, AmbientM.branch, after, mark,
    allowedMasked, allowedBits, zero]
  all_goals rfl

/-- The original arbitrary owner predicate, through the actual native lift. -/
theorem readNode_ipv4 (n : AipNode) (width : n.bitlen = 32)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Product.Returns (liftWG (readNode n)) (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun result w => P w.wg w.fs w.tasks w.seccomp ∧
        result = (4, allowedMasked true n.bits n.cidr, n.cidr)) := by
  intro w pre
  obtain ⟨result, current, after, run, preserved, exactResult⟩ :=
    ((returns_iff _ _ _).mpr (readNode_ipv4_native n width
      (fun g => P g w.fs w.tasks w.seccomp))) w.wg w.ambient pre
  refine ⟨result, {w with wg := current, ambient := after}, ?_, preserved, exactResult⟩
  change (Except.bind (((readNode n).run w.wg).run w.ambient) _) = _
  rw [run]
  rfl

end Leanux.Proofs.WG.Config
