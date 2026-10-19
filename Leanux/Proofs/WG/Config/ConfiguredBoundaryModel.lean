import Leanux.Proofs.WG.Config.ConfiguredOwnerModel
import Leanux.Proofs.WG.Index.ConfigurationCoreModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

def DeviceReady (d : Device) : Prop :=
  ∃ t4 t6, RoutingInvariant d t4 t6 ∧ ConfiguredOwners d t4 t6

def ProjectedReady (s : Campaign2.Snapshot) : Prop :=
  ∃ d,s.wg.device=some d ∧ DeviceReady d

def ProjectedEntry (cs : Ledger) (loans : Reservations) (s : Campaign2.Snapshot) : Prop :=
  Index.View.ConfigurationInput cs loans s ∧ ProjectedReady s

def ProjectedSelected (cs : Ledger) (loans : Reservations) (pid : PeerId)
    (s : Campaign2.Snapshot) : Prop :=
  ProjectedEntry cs loans s ∧ ∃ d,s.wg.device=some d ∧ pid∈d.peerList

end Leanux.Proofs.WG.Config.OwnerConfiguration
