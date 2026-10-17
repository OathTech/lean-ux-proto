import Leanux.Proofs.WG.Index.OwnerWordModel

set_option autoImplicit false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Acquiring the referenced peer and updating an independently located owner
word preserve that peer's tag, including when owner and referenced peer alias. -/
theorem lookup_acquire_owner_tag (d : Device) (owner : IndexOwner)
    (pid : PeerId) (p : Peer) :
    ((Index.writeOwnerWord (Index.acquirePeer d pid p) owner (some pid)).peers[pid]?).map
      Peer.handshakeState = some p.handshakeState := by
  cases owner with
  | keypair kp =>
    cases key : d.keypairs[kp]? <;>
      simp [Index.writeOwnerWord, Index.acquirePeer, key]
  | handshake own =>
    by_cases same : own = pid
    · subst own
      simp [Index.writeOwnerWord, Index.acquirePeer]
    · have other : pid ≠ own := Ne.symm same
      cases peer : d.peers[own]? with
      | none =>
        simp [Index.writeOwnerWord, Index.acquirePeer, Std.TreeMap.getElem?_insert,
          other, peer]
      | some q =>
        simp [Index.writeOwnerWord, Index.acquirePeer, Std.TreeMap.getElem?_insert,
          Std.TreeMap.getElem_insert, same, other, peer]
end Leanux.Proofs.WG.Noise
