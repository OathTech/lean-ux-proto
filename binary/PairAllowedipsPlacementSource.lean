import PairAllowedipsPlacement

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG

/-- Exposing correspondence points does not change the source program. -/
theorem run_eq_source (root : Option NodeId) (key cidr bits : Nat) :
    run root key cidr bits=WG.nodePlacement root key cidr bits := by
  unfold run WG.nodePlacement
  congr 1
  funext acc
  cases acc.1 <;> rfl

#print axioms run_eq_source
end Binary.Pair.Allowedips.Placement
