import Leanux.Proofs.WG.Config.AllowedTransferModel
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
theorem placement_first (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (owner : Option PeerId) (parent : Slot) (width : cidr ≤ allowedBits v4)
    (resident : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) owner with parent }) :
    Returns (nodePlacement (some id) addr cidr (allowedBits v4))
      (fun w => w.k.wg = some d)
      (fun result w => result = (some id, true) ∧ w.k.wg = some d) := by
  have hg : ⦃fun w => ⌜w.k.wg = some d⌝⦄ getNode id
      ⦃⇓ n w => ⌜n = { newNode addr cidr (allowedBits v4) owner with parent } ∧ w.k.wg = some d⌝⦄ := by
    mvcgen [getNode, getDev, getK, invariant]
    all_goals simp_all
  rw [returns_iff]
  simp only [nodePlacement]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.div_one]
  rw [List.range'_succ, List.forIn_cons]
  mvcgen [branch, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals cases v4
  all_goals simp only [newNode, allowedBits, Bool.false_eq_true, ite_false, ite_true] at *
  all_goals mvcgen [branch, branchCmp, prefixMatches, commonBits, fls]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
end Leanux.Proofs.WG.Config
