import Leanux.Proofs.WG.Progress.AllowedFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.AllowedFinite
open Leanux Leanux.WG

/-- Original node allocation lifted to the actual WG state, with all original
allocation outcomes and missing-device Stops retained. -/
theorem original_allocate_finite (site : AllocSite) (node : AipNode) :
    Campaign2.AgreesOn (fun _ => True) (liftAip (WG.allocNode site node))
      (liftAip (allocate site node)) := by
  rw [allocate_source]
  intro g ambient pre
  rfl

/-- Exact finite original trie add, including all three allocation sites,
bounded placement and actual replacement/rollback effects. -/
theorem original_add_finite (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.add root bits key cidr peer)
      (add root bits key cidr peer) := by
  rw [add_source]
  intro g ambient pre
  rfl

/-- Exact finite original insertion with the original sequence increment and
family selection. No well-formedness, residency or successful-allocation premise. -/
theorem original_insert_finite (family addr cidr : Nat) (peer : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.insert family addr cidr peer)
      (insert family addr cidr peer) := by
  rw [insert_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.AllowedFinite
