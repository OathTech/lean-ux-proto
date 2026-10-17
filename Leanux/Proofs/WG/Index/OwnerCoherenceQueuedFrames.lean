import Leanux.Proofs.WG.Index.OwnerCoherenceFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceSessionFrames
import Leanux.Proofs.WG.Config.QueuedHandshake

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- The actual queue-inspection effect preserves every hashed owner. Repeated
writes to the selected peer are compared pointwise, including the acquired
reference restored on a normal already-queued refusal. -/
theorem queuedDeviceAfterInspection_owner_coherent (d : Device) (pid : PeerId)
    (p : Peer) (now : Int64) (queued : Bool) (resident : d.peers[pid]? = some p)
    (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (Config.queuedDeviceAfterInspection d pid p now queued) := by
  unfold Config.queuedDeviceAfterInspection
  split
  · exact coherent
  · let acquired := Config.withPeer d pid {p with refcount := p.refcount + 1}
    have acquiredCoherent : HashedOwnersCoherent acquired := by
      intro e member
      exact ownerCoherent_acquire d pid p resident e.owner (coherent e member)
    split
    · let restored := Config.withPeer acquired pid p
      have peers (target : PeerId) : restored.peers[target]? = d.peers[target]? := by
        by_cases same : pid = target
        · subst target
          simp [restored,Config.withPeer,resident]
        · simp [restored,acquired,Config.withPeer,Std.TreeMap.getElem?_insert,same]
      change HashedOwnersCoherent restored
      intro e member
      obtain ⟨target,q,word,found,positive,identity⟩ := coherent e member
      refine ⟨target,q,?_,(peers target).trans found,positive,?_⟩
      · cases kind : e.owner with
        | handshake own => simpa only [kind,ownerWord,peers] using word
        | keypair id => simpa only [kind,ownerWord,restored,acquired,Config.withPeer] using word
      · cases kind : e.owner with
        | handshake own => simpa only [kind] using identity
        | keypair id => simpa only [kind,restored,acquired,Config.withPeer] using identity
    · let q : Peer := {p with refcount := p.refcount + 1, handshakePending := true}
      have pendingCoherent := peerWrite_owner_coherent acquired pid
        {p with refcount := p.refcount + 1} q
        (by simp [acquired,Config.withPeer]) rfl rfl acquiredCoherent
      exact pendingCoherent

end Leanux.Proofs.WG.Index
