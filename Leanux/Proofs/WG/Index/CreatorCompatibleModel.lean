import Leanux.Proofs.WG.Index.OwnerCoherenceCreatorModel
import Leanux.Proofs.WG.Peers.ConfiguredIdentity

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- A resident caller has a positive reference and either NULL or its own
embedded word. This does not assert record readiness or non-NULL publication. -/
def HandshakeCompatible (pid : PeerId) (d : Device) : Prop :=
  HashedOwnersCoherent d ∧ ∀ p, d.peers[pid]? = some p →
    ConfiguredIdentity.Self p.handshakeEntryPeer pid ∧ 0 < p.refcount

def View.HandshakeCompatibleSafe (pid : PeerId) (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → HandshakeCompatible pid d

end Leanux.Proofs.WG.Index
