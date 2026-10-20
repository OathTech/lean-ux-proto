import SourceAdapter
import LookupProjection
import MirrorPeerPoints

namespace Binary.LookupRelation
open Leanux Leanux.WG

/-- Decision worlds retain the old count, including dead=false. -/
theorem project_peerPoint (c : Config) (world : World) (peer : Peer)
    (point : MirrorHistory.Point) (member : point ∈ MirrorHistory.peerPoints world peer) :
    project c point.world = project c world := by
  unfold project
  rw [MirrorHistory.peerPoints_kernel world peer point member]

/-- Updating a peer count does not replace its embedded handshake owner
    word, including when the selected owner is that same peer. -/
theorem owner_value_count_update (device : Device) (pid : PeerId) (peer : Peer) (count : Nat)
    (present : device.peers.get? pid = some peer) (owner : IndexOwner) :
    OwnerWord.value {device with peers := device.peers.insert pid {peer with refcount := count}} owner =
      OwnerWord.value device owner := by
  cases owner with
  | keypair id => rfl
  | handshake id =>
    have present : device.peers[pid]? = some peer := present
    by_cases same : pid = id
    · subst id
      simp [OwnerWord.value,  present]
    · simp [OwnerWord.value, Std.TreeMap.getElem?_insert, same]

/-- The exact returned source projection. Zero is a present dead peer;
    it is not replaced by an erased-peer abstraction. -/
theorem project_peerFinal (c : Config) (world : World) (device : Device)
    (pid : PeerId) (peer : Peer) (v : View)
    (hasDevice : world.wg.dev = some device) (hasPeer : device.peers.get? pid = some peer)
    (focused : c.focus.peer = some pid) (projected : project c world = some v) :
    project c (PeerMirror.peerFinal pid world peer) =
      some (if peer.refcount = 0 then v else {v with count := some (peer.refcount+1)}) := by
  have hasPeer' : device.peers[pid]? = some peer := hasPeer
  have view : v = {
      bucket := device.indexTable.filter (fun e => e.index % 8192 == c.query % 8192)
      ownerWord := c.focus.owner.bind (OwnerWord.value device)
      count := some peer.refcount } := by
    simpa [project, hasDevice, focused, hasPeer'] using projected.symm
  subst v
  have words : OwnerWord.value
      {device with peers := device.peers.insert pid {peer with refcount := peer.refcount+1}} =
      OwnerWord.value device := by
    funext owner
    exact owner_value_count_update device pid peer (peer.refcount+1) hasPeer owner
  by_cases zero : peer.refcount = 0 <;>
    simp [PeerMirror.peerFinal, project, PeerMirror.countRecords, PeerMirror.recordCmp,
      LookupMirror.record, hasDevice, focused, hasPeer', zero, words]

#print axioms project_peerPoint
#print axioms owner_value_count_update
#print axioms project_peerFinal
end Binary.LookupRelation
