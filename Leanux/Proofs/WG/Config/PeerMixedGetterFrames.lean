import Leanux.Proofs.WG.Config.MultiMixedEffects
import Leanux.Proofs.WG.Config.PeerPagePlanModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual mixed update retains cursor lifetime fields and exact fixed
serialization cost at every initially resident peer. -/
theorem multiMixedEffect_cursor_fields (d final : Device) (mark : Nat) (pid q : PeerId)
    (psk : Key) (interval : Nat) (p : Peer)
    (effect : MultiMixedEffect d mark pid psk interval final)
    (resident : d.peers[q]? = some p) :
    ∃ next, final.peers[q]? = some next ∧ next.refcount = p.refcount ∧
      next.isDead = p.isDead ∧ peerFixedSpace next = peerFixedSpace p := by
  obtain ⟨cleared,selected,_,clears,selectedResident,rfl⟩ := effect
  obtain ⟨next,nextResident,shape⟩ := clearedPeerStore_resident d cleared d.peerList clears q p resident
  by_cases same : q = pid
  · subst q
    have samePeer : selected = next := Option.some.inj (selectedResident.symm.trans nextResident)
    subst selected
    refine ⟨_,scalarDevice_peer cleared pid next psk interval,?_,?_,?_⟩
    · rcases shape with rfl | ⟨reset,rfl⟩ <;> rfl
    · rcases shape with rfl | ⟨reset,rfl⟩ <;> rfl
    · rcases shape with rfl | ⟨reset,rfl⟩
      · rfl
      · cases endpoint : p.endpoint <;> simp [peerFixedSpace,clearedSource,endpoint]
  · refine ⟨next,?_,?_,?_,?_⟩
    · simpa [scalarDevice,withPeer,Std.TreeMap.getElem?_insert,same,Ne.symm same] using nextResident
    · rcases shape with rfl | ⟨reset,rfl⟩ <;> rfl
    · rcases shape with rfl | ⟨reset,rfl⟩ <;> rfl
    · rcases shape with rfl | ⟨reset,rfl⟩
      · rfl
      · cases endpoint : p.endpoint <;> simp [peerFixedSpace,clearedSource,endpoint]

end Leanux.Proofs.WG.Config
