import Leanux.Proofs.WG.Index.OwnerCoherenceModel

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Publishing a handshake requires its own live, resident self-referencing
owner even when that owner is not already in the table. This is a local
preservation invariant, not reachability or readiness of recorded inputs. -/
def HandshakePublisher (pid : PeerId) (d : Device) : Prop :=
  HashedOwnersCoherent d ∧ OwnerCoherent d (.handshake pid)

namespace View
def HandshakePublisherSafe (pid : PeerId) (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → HandshakePublisher pid d
end View

end Leanux.Proofs.WG.Index
