import Leanux.Proofs.WG.Index.IncomingIndexClaims
import Leanux.Proofs.WG.Index.ReachedIndexSource
import Leanux.Proofs.WG.Index.LookupCoreSource
import Leanux.Proofs.WG.Lifetimes.HandshakeCalls
import Leanux.Proofs.WG.Queues.HandshakeArms
import Leanux.Proofs.WG.Index.ResponseIndexSource
import Leanux.Proofs.WG.Index.StagingIndexSource
import Leanux.Proofs.WG.Index.ReceiveFrames
import Leanux.Proofs.WG.Config.EndpointSetSource
import Leanux.Proofs.WG.Roaming.EndpointSource
import Leanux.Proofs.WG.Lifetimes.MaintenanceCalls
import Leanux.Proofs.WG.Lifetimes.TxStagingCalls

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders
namespace Incoming

/-- Native intermediate cut. The allocation witness supplies bounds at this
actual state; it does not claim a particular outer RxHistory journal. -/
def Cut (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  (∃ history, AllocationInv history w) ∧
  HandshakeResponse.Input cs loans w ∧ BaseCoherence.Inv w ∧ Reached.Core w

def Selected (cs : Ledger) (loans : Reservations) (peer : Option PeerId) (w : WGWorld) : Prop :=
  match peer with
  | none => Cut cs loans w
  | some pid => ∃ paid : Owner,paid.slot=pid ∧ Cut cs (paid::loans) w


end Incoming
end Leanux.Proofs.WG.Index
