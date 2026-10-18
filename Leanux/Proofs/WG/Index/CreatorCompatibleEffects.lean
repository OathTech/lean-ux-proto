import Leanux.Proofs.WG.Index.CreatorCompatibleModel
import Leanux.Proofs.WG.Index.OwnerCoherenceSessionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

theorem peerWrite_handshakeCompatible (pid : PeerId) (d : Device) (p q : Peer)
    (resident : d.peers[pid]? = some p)
    (word : q.handshakeEntryPeer = p.handshakeEntryPeer)
    (count : q.refcount = p.refcount) (compatible : HandshakeCompatible pid d) :
    HandshakeCompatible pid {d with peers := d.peers.insert pid q} := by
  refine ⟨peerWrite_owner_coherent d pid p q resident word count compatible.1,?_⟩
  intro actual found
  have equal : actual = q := by simpa using found.symm
  subst actual
  simpa only [word,count] using compatible.2 p resident

end Leanux.Proofs.WG.Index
