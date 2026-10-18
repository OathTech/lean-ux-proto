import Leanux.Proofs.WG.Noise.InitialSlotCredits
import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.SessionCoherenceModel
import Leanux.Proofs.WG.Queues.RunnerAccount
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.InitializedBounds
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

/-! Model: data-only endpoint facts. These allow absent keys and nullable owner
words; they assert neither hashed coherence nor positive reference credits. -/
structure EndpointBounds (d : Device) : Prop where
  slots : CurrentSlots.SlotInv (Affiliation.state d)
  peers : ∀ pid p, d.peers[pid]? = some p → pid < d.nextPeer
  keys : KeypairStoreBounded d

def EndpointSafe (entry : Campaign2.Snapshot) : Prop :=
  ∀ d, entry.wg.device = some d → EndpointBounds d

abbrev Inspection := Except (Nat × Stop) (Json × Campaign2.Snapshot)


end Leanux.Proofs.WG.Index.InitializedBounds
