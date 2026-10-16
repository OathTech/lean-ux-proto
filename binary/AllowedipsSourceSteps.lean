import AllowedipsLoopSetup

namespace Binary.AllowedipsSource
open Leanux Leanux.WG AllowedipsRelation

/-- Source early exits carry exactly the returned found-node accumulator. -/
theorem done_shape (view : NodeView) (bits key id : Nat) (previous : Option NodeId)
    (node : AipNode) (acc : Acc) (present : view id = some node)
    (selected : selectStep view bits key (none,some id,previous) = some (.done acc)) :
    acc.1 = some acc.2.2 := by
  by_cases mismatch : commonValue node key bits < node.cidr <;>
    by_cases full : node.cidr = bits <;>
    by_cases invalid : node.cidr ≥ node.bitlen <;>
    cases child : node.bit[key/2^(node.bitlen-1-node.cidr)%2]?
  all_goals try simp only [full] at mismatch
  all_goals simp [selectStep,present,mismatch,full,invalid,child] at selected
  all_goals cases selected; rfl

/-- A yielded source step follows exactly the represented chosen child. -/
theorem yield_shape (view : NodeView) (bits key id : Nat) (previous : Option NodeId)
    (node : AipNode) (acc : Acc) (present : view id = some node)
    (selected : selectStep view bits key (none,some id,previous) = some (.yield acc)) :
    acc.1 = none ∧
    node.cidr ≤ common bits node.bits key ∧ node.cidr ≠ bits ∧
    node.bit[childIndex node key]? = some acc.2.1 ∧
    acc.2.2 = AllowedipsLoop.selectedNode id node previous := by
  by_cases mismatch : commonValue node key bits < node.cidr <;>
    by_cases full : node.cidr = bits <;>
    by_cases invalid : node.cidr ≥ node.bitlen <;>
    cases child : node.bit[key/2^(node.bitlen-1-node.cidr)%2]?
  all_goals try simp only [full] at mismatch
  all_goals simp [selectStep,present,mismatch,full,invalid,child] at selected
  all_goals cases selected
  all_goals
    refine ⟨rfl,?_,full,child,rfl⟩
    rw [←AllowedipsLoop.common_value]
    omega

#print axioms done_shape
#print axioms yield_shape
end Binary.AllowedipsSource
