import Leanux.Proofs.WG.Index.ReachedIndexModel
import Leanux.Proofs.WG.Index.InitializedBoundsModel
import Leanux.Proofs.WG.Index.CreatorCompatibleModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

def ResponseIndexPrefix (pid : PeerId) (g : WGWorld) : Prop :=
  (∀ d,g.dev=some d → InitializedBounds.EndpointBounds d) ∧
  (∀ d,g.dev=some d → HandshakeCompatible pid d) ∧
  (∀ d,g.dev=some d → HashSlotCoverage d) ∧
  (∀ d,g.dev=some d → DeadHashedReserved [] d)

def ResponseIndexState (g : WGWorld) : Prop :=
  ∀ d,g.dev=some d → HashSlotCoverage d ∧ HashedOwnersCoherent d ∧ DeadHashedReserved [] d

end Leanux.Proofs.WG.Index
