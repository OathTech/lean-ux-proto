import Leanux.Proofs.WG.Roaming.RemoteProvenanceModel
import Leanux.Proofs.WG.Roaming.RemoteDriverBridge
import Leanux.Proofs.WG.Roaming.ConsumptionAuthenticationBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged

namespace RemoteProvenance
/-- Internal relation to the actual journal. Raw execution states and witnesses
stay behind this bridge; each public constructor contains projections only. -/
def Matches (trace : Runner.Trace) (placeholders : Bool)
    (events : List RemoteDriver.Event) : Origin → Prop
  | .configuration receipt =>
    ∃ run, RemoteDriver.Event.endpoint run ∈ events ∧ run.Valid ∧ run.projects = receipt
  | .handshake observation =>
    ∃ run, RemoteDriver.Event.receive run ∈ events ∧ run.Valid (liftWG receiveStep) ∧
      ReceiveStepRemote.Matches run observation
  | .data q e =>
    ConfirmationOrder.OccursAt trace placeholders q ∧ e.Valid trace placeholders q ∧
    ∃ occurrence skb stamp receipt,
      RemoteDriver.Event.rx (.consumed occurrence skb stamp receipt) ∈ events ∧
      ConfirmationOrder.Matches q.position occurrence skb stamp receipt q

end RemoteProvenance
end Leanux.Proofs.WG.Roaming
