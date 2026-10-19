import Leanux.Proofs.WG.Queues.HolderBaseRetirement
import Leanux.Proofs.WG.Queues.BaseCoherenceRemoval
import Leanux.Proofs.WG.Configuration.PeerRemovalCompletion
import Leanux.Proofs.WG.Config.ReplacementInitialSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.ReplaceCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Queues.RxCredits Queues.RxCredits.DurableHolders AllowedIps Std.Do Lifetimes

def Input (cs : Ledger) (loans : Reservations) (tables : FlatTable × FlatTable)
    (w : WGWorld) : Prop :=
  DurableHolders.Boundary cs loans w ∧ BaseCoherence.Inv w ∧
    RoutedView (routingView w) tables

def Empty (w : WGWorld) : Prop :=
  ∃d, w.dev=some d ∧ d.peerList=[] ∧ d.peerHashtable=[] ∧
    RoutedView (routingView w) ([],[])

namespace View

/-- Initial-state funding and structural assumptions through the campaign
projection. The witnesses describe this entry state, not a successful run or
a chosen final state. -/
def Input (cs : Ledger) (loans : Reservations) (tables : FlatTable × FlatTable)
    (s : Campaign2.Snapshot) : Prop :=
  ∃w a, Campaign2.snapshot w a=s ∧ ReplaceCompletion.Input cs loans tables w

/-- No configured peers, no public-key rows, and empty represented routes.
Resident peer/key/node stores may still contain allocations. -/
def Empty (s : Campaign2.Snapshot) : Prop :=
  ∃d, s.wg.device=some d ∧ d.peerList=[] ∧ d.peerHashtable=[] ∧
    RoutedView (s.wg.device.map routingState) ([],[])

end View

end Leanux.Proofs.WG.Config.ReplaceCompletion
