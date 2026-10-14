import Leanux.Proofs.WG.AllowedIps.RoutingLifecycle
import Leanux.Runner

/-! Initialization from the original configured network fixture, without
assuming that arbitrary parsed configuration operations preserve routing. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem empty_routing (ifindex : Nat) (ifname : String) :
    RoutingInvariant ({ifindex, ifname} : WG.Device) .empty .empty := by
  constructor
  · exact ⟨rfl, rfl, True.intro, True.intro⟩
  · trivial
  · trivial
  · trivial
  · trivial
  · exact List.nodup_nil
  · exact List.nodup_nil
  · intro id n hn
    simp at hn
  · intro pid p hp
    simp at hp
  · intro e he
    simp [Tree.entries] at he
  · intro pid p hp
    simp at hp

/-- This is the actual Runner fixture with its configured WG device. The
non-network and bare fixtures have no device and are not silently identified
with an empty resident device. -/
theorem initialKernel_routing (rlimit : Nat) (foreign stepped seccompChild : Bool) :
    ∃ d, (Runner.initialKernel rlimit true false foreign stepped seccompChild).wg = some d ∧
      RoutingInvariant d .empty .empty :=
  ⟨{ifindex := 3, ifname := "wg0"}, rfl, empty_routing 3 "wg0"⟩

end Leanux.Proofs.WG.AllowedIps
