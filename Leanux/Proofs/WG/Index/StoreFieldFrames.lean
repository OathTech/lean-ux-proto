import Leanux.Proofs.WG.Index.ReleaseModel

/-! Existing preservation support, separated from state-changing effects. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

theorem acquirePeer_word (d : Device) (pid : PeerId) (p : Peer) (owner : IndexOwner)
    (old : Option PeerId) (peer : d.peers[pid]? = some p)
    (resident : ownerWord d owner = some old) :
    ownerWord (acquirePeer d pid p) owner = some old := by
  cases owner with
  | handshake own =>
    by_cases same : pid = own
    · subst own; simpa [ownerWord, acquirePeer, peer] using resident
    · simpa [ownerWord, acquirePeer, Std.TreeMap.getElem?_insert, same] using resident
  | keypair kp => exact resident

theorem released_other_keypair (d : Device) (id other : KeypairId) (k : Keypair) (now : Bool)
    (different : id ≠ other) :
    (releasedDevice d id k now).keypairs[other]? = d.keypairs[other]? := by
  cases now <;> by_cases last : k.refcount = 1 <;>
    simp [releasedDevice, unhashKeypair, last, Std.TreeMap.getElem?_insert,
      Std.TreeMap.getElem?_erase, different]

theorem released_next (d : Device) (id : KeypairId) (k : Keypair) (now : Bool) :
    (releasedDevice d id k now).nextKeypairId = d.nextKeypairId := by
  cases now <;> by_cases last : k.refcount = 1 <;>
    simp [releasedDevice, unhashKeypair, last]

theorem releasedPeer_other (pid other : PeerId) (d : Device) (p : Peer) (different : pid ≠ other) :
    (releasedPeerDevice d pid p).peers[other]? = d.peers[other]? := by
  unfold releasedPeerDevice
  split <;> simp [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert, different]

theorem releasedPeer_next (pid : PeerId) (d : Device) (p : Peer) :
    (releasedPeerDevice d pid p).nextKeypairId = d.nextKeypairId := by
  unfold releasedPeerDevice
  split <;> rfl

theorem releasedPeer_keypairs (pid : PeerId) (d : Device) (p : Peer) :
    (releasedPeerDevice d pid p).keypairs = d.keypairs := by
  unfold releasedPeerDevice
  split <;> rfl

end Leanux.Proofs.WG.Index
