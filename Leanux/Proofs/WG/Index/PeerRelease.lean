import Leanux.Proofs.WG.Index.ReleaseBounds

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Actual ordered peer writes: decrement first, then unhash and erase on the last put. -/
def releasedPeerDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  let decremented := { d with peers := d.peers.insert pid { p with refcount := p.refcount - 1 } }
  if p.refcount = 1 then
    { decremented with
      indexTable := removeOwner (.handshake pid) decremented.indexTable
      txDropped := decremented.txDropped + p.staged.length, peers := decremented.peers.erase pid }
  else decremented

theorem peerPut_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) :
    Returns (peerPut (some pid)) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (releasedPeerDevice d pid p)) := by
  rw [returns_iff]
  by_cases last : p.refcount = 1
  all_goals noise_vcgen [peerPut, requireNotPending, refcountDecAndTest,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, branchCmp, invariant, unsupported, retirePeerUnits, indexRemove,
    _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all only [Option.map_some, Option.some.injEq]
  all_goals subst_vars
  all_goals simp_all [releasedPeerDevice, removeOwner]
  all_goals grind only

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

theorem releasedPeer_other (pid other : PeerId) (d : Device) (p : Peer) (different : pid ≠ other) :
    (releasedPeerDevice d pid p).peers[other]? = d.peers[other]? := by
  unfold releasedPeerDevice
  split <;> simp [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert, different]

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

theorem releasedPeer_next (pid : PeerId) (d : Device) (p : Peer) :
    (releasedPeerDevice d pid p).nextKeypairId = d.nextKeypairId := by
  unfold releasedPeerDevice
  split <;> rfl

theorem releasedPeer_keypairs (pid : PeerId) (d : Device) (p : Peer) :
    (releasedPeerDevice d pid p).keypairs = d.keypairs := by
  unfold releasedPeerDevice
  split <;> rfl

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
