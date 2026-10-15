import Leanux.Proofs.WG.Index.StoreFieldFrames
import Leanux.Proofs.WG.Index.ReleaseModel

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

theorem releasedPeer_table (pid : PeerId) (d : Device) (p : Peer) :
    (releasedPeerDevice d pid p).indexTable =
      if p.refcount = 1 then removeOwner (.handshake pid) d.indexTable else d.indexTable := by
  unfold releasedPeerDevice
  split <;> rfl

theorem releasedPeer_peer (pid : PeerId) (d : Device) (p : Peer) :
    (releasedPeerDevice d pid p).peers[pid]? =
      if p.refcount = 1 then none else some { p with refcount := p.refcount - 1 } := by
  unfold releasedPeerDevice
  split <;> simp

theorem releasedPeer_indices (pid : PeerId) (d : Device) (p : Peer)
    (unique : UniqueIndices d.indexTable) : UniqueIndices (releasedPeerDevice d pid p).indexTable := by
  rw [releasedPeer_table]
  split
  · exact remove_indices _ _ unique
  · exact unique

theorem releasedPeer_owners (pid : PeerId) (d : Device) (p : Peer)
    (unique : UniqueOwners d.indexTable) : UniqueOwners (releasedPeerDevice d pid p).indexTable := by
  rw [releasedPeer_table]
  split
  · exact remove_owners _ _ unique
  · exact unique

theorem releasedPeer_dropped (pid : PeerId) (d : Device) (p : Peer) :
    (releasedPeerDevice d pid p).txDropped =
      d.txDropped + (if p.refcount = 1 then p.staged.length else 0) := by
  unfold releasedPeerDevice
  split <;> simp_all

theorem releasedPeer_owners_bounded (pid : PeerId) (d : Device) (p : Peer)
    (bounded : KeypairOwnersBounded d) : KeypairOwnersBounded (releasedPeerDevice d pid p) := by
  intro e member id owner
  rw [releasedPeer_next]
  apply bounded e _ id owner
  rw [releasedPeer_table] at member
  split at member
  · exact (List.mem_filter.mp member).1
  · exact member

theorem releasedPeer_store_bounded (pid : PeerId) (d : Device) (p : Peer)
    (bounded : KeypairStoreBounded d) : KeypairStoreBounded (releasedPeerDevice d pid p) := by
  intro id k resident
  rw [releasedPeer_next]
  rw [releasedPeer_keypairs] at resident
  exact bounded id k resident

end Leanux.Proofs.WG.Index
