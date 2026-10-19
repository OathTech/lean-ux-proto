import Leanux.Proofs.WG.Config.ConfiguredBoundaryModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

theorem configured_of_list (d out : Device) (t4 t6 : Tree)
    (owners : ConfiguredOwners d t4 t6)
    (kept : ∀ pid ∈ d.peerList, pid ∈ out.peerList) :
    ConfiguredOwners out t4 t6 :=
  fun e member => kept e.peer (owners e member)

end Leanux.Proofs.WG.Config.OwnerConfiguration
