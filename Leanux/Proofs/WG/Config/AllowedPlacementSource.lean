import Leanux.Proofs.WG.Config.AllowedInsertModel
import Leanux.Proofs.WG.Config.Returns
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
theorem placement_first (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (owner : Option PeerId) (parent : Slot) (width : cidr ≤ allowedBits v4)
    (resident : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) owner with parent }) :
    Returns (liftAip (nodePlacement (some id) addr cidr (allowedBits v4)))
      (fun g => g.dev = some d)
      (fun result g => result = (some id, true) ∧ g.dev = some d) := by
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let cmp (a : Ambient) (decision : Decision) : Ambient :=
    {a with steps := a.steps.push {decision, outcome := true, operands := some (Int.ofNat cidr, Int.ofNat cidr), netRx := a.netRxSection}}
  let middle := cmp (mark ambient .placementNode true) .placementCidrLe
  let trail := if v4 then mark middle .commonBits32 true else
    mark (mark (mark middle .commonBits32 false) .commonBits128 true) .fls128High false
  let after := cmp (mark trail .placementPrefixMatches true) .placementExact
  cases v4
  all_goals
    simp only [allowedBits, Bool.false_eq_true, ite_false, ite_true] at width resident ⊢
    refine ⟨(some id, true), {g with dev := some d}, after, ?_, rfl, rfl⟩
    simp only [nodePlacement]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.div_one]
    rw [List.range'_succ, List.forIn_cons]
    simp [liftAip, getDev, modifyDev, device, branch, AmbientM.branch, branchCmp,
      AmbientM.branchCmp, getNode, resident, newNode, prefixMatches, commonBits, fls, width, Nat.not_lt.mpr width, after, trail, middle, cmp, mark]
    rfl
end Leanux.Proofs.WG.Config
