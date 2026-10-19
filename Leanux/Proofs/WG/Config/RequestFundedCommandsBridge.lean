import Leanux.Proofs.WG.Config.RequestFundedCommandsModel
import Leanux.Proofs.WG.Config.RequestCommandBridge
import Leanux.Proofs.WG.Config.ConfiguredBoundaryBridge

/-! Projected nested facts retain a hidden same-call native witness for the actual entry and exit accounts. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
open Leanux Leanux.WG Queues Queues.RxCredits AllowedIps Configuration
open Leanux.Proofs.Logged
open Leanux.Proofs.WG.Config.OwnerConfiguration

/-- The account belongs to the exact same native call already identifying the
nested command inspection. Remaining durable holders may change across it. -/
def AccountMatches (cs : Ledger) (loans : Reservations)
    (r : Receipt) (p : PeerAttrs) (nested : AllowedOrder.Inspection) : Prop :=
  ∃native : WGRunWitness Int,native.Valid (setPeerCmd p) ∧
    receipt (.peer p) native=r ∧
    CommandOrder.inspection p native.before native.ambientBefore=nested ∧
    Entry cs loans native.before ∧ Entry cs loans native.after

def RoutedCommands (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (result : Inspection) : Prop :=
  ∀(i : Nat) (r : Receipt) (p : PeerAttrs),
    (peerReceipts result.receipts)[i]?=some r → r.kind=.peer p →
    (attrs.peers.getD [])[i]?=some (.attrs p) ∧
      ProjectedEntry cs loans r.before ∧ ProjectedEntry cs loans r.after ∧
      ∃tables nested,PeerCommandFacts r p nested ∧
        AccountMatches cs loans r p nested ∧
        RoutedView (r.before.wg.device.map routingState) tables ∧
        AllowedOrder.RoutedFacts tables nested

end Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
