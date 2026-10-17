import Leanux.Proofs.WG.Config.TwoPageCallbackModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.TwoPage
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual two writes restore every lookup; no raw-tree extensionality is used. -/
theorem cursorReleasedHeld_lookup (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (positive : 0 < p.refcount) (id : PeerId) :
    (cursorReleased (cursorAcquired d (some pid)) (some pid)).peers[id]? = d.peers[id]? := by
  have nonzero : p.refcount ≠ 0 := by omega
  by_cases same : pid = id
  · subst id
    simp [cursorReleased,cursorAcquired,resident,Index.releasedPeerDevice,nonzero]
  · simp [cursorReleased,cursorAcquired,resident,Index.releasedPeerDevice,nonzero,
      Std.TreeMap.getElem?_insert,same]

/-- Holding the cursor changes no serializer or list input, including endpoints. -/
theorem heldPeer_dump_fields (p : Peer) :
    peerFixedSpace {p with refcount := p.refcount+1} = peerFixedSpace p ∧
    peerFixedAttrs {p with refcount := p.refcount+1} = peerFixedAttrs p := ⟨rfl,rfl⟩

/-- Cursor acquisition preserves every input consumed by empty-IP serialization. -/
theorem heldPeers_dump (peers : PeerId → Peer) (cursor : PeerId) (ids : List PeerId) :
    multiPeerSpace (heldPeers peers cursor) ids = multiPeerSpace peers ids ∧
    multiPeerParts (heldPeers peers cursor) ids = multiPeerParts peers ids := by
  have fields (id : PeerId) :
      peerFixedSpace (heldPeers peers cursor id) = peerFixedSpace (peers id) ∧
      peerFixedAttrs (heldPeers peers cursor id) = peerFixedAttrs (peers id) ∧
      (heldPeers peers cursor id).remoteStatic = (peers id).remoteStatic := by
    simp only [heldPeers]
    split <;> exact ⟨rfl,rfl,rfl⟩
  simp only [multiPeerSpace,multiPeerParts,(fields _).1,(fields _).2.1,(fields _).2.2,and_self]

/-- Exact native outer-device effects of the ordered cursor writes. -/
theorem cursorHeld_device_fields (d : Device) (cursor : PeerId) (p : Peer)
    (resident : d.peers[cursor]? = some p) (positive : 0 < p.refcount) :
    {cursorAcquired d (some cursor) with peers := d.peers} = d ∧
    {cursorReleased (cursorAcquired d (some cursor)) (some cursor) with peers := d.peers} = d := by
  have nonzero : p.refcount ≠ 0 := by omega
  simp [cursorAcquired,cursorReleased,resident,Index.releasedPeerDevice,nonzero]

end Leanux.Proofs.WG.Config.TwoPage
