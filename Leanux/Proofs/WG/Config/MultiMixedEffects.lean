import Leanux.Proofs.WG.Config.MultiMixedModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- A clear-list effect preserves residency and identifies the original peer
or its actual source-cleared successor, without assuming list membership. -/
theorem clearedPeerStore_resident (initial current : Device) (seen : List PeerId)
    (effect : ClearedPeerStore initial current seen) (pid : PeerId) (p : Peer)
    (resident : initial.peers[pid]? = some p) :
    ∃ next, current.peers[pid]? = some next ∧
      (next = p ∨ ∃ reset, next = clearedSource p reset) := by
  by_cases member : pid ∈ seen
  · obtain ⟨old,reset,before,after⟩ := (show ∃ old reset,
        initial.peers[pid]? = some old ∧ current.peers[pid]? = some (clearedSource old reset) by
      simpa only [ClearedPeerStore,member,ite_true] using effect pid)
    rw [resident] at before
    cases before
    exact ⟨_,after,Or.inr ⟨reset,rfl⟩⟩
  · have same : current.peers[pid]? = initial.peers[pid]? := by
      simpa only [member,ite_false] using effect pid
    exact ⟨p,same.trans resident,Or.inl rfl⟩

/-- Each initially resident peer retains its dump-relevant fields except the
selected scalars; source/cache clearing still has its exact separate effect. -/
theorem multiMixedEffect_peer (d final : Device) (mark : Nat) (pid q : PeerId)
    (psk : Key) (interval : Nat) (p : Peer)
    (effect : MultiMixedEffect d mark pid psk interval final)
    (resident : d.peers[q]? = some p) :
    ∃ next, final.peers[q]? = some next ∧ next.allowedipsList = p.allowedipsList ∧
      next.remoteStatic = p.remoteStatic ∧
      peerFixedAttrs next = peerFixedAttrs
        (if q = pid then {p with presharedKey := psk,persistentKeepaliveInterval := interval} else p) := by
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
      · simp only [ite_true]
      · cases endpoint : p.endpoint <;> simp [peerFixedAttrs,clearedSource,endpoint]
  · refine ⟨next,?_,?_,?_,?_⟩
    · simpa [scalarDevice,withPeer,Std.TreeMap.getElem?_insert,same,Ne.symm same] using nextResident
    · rcases shape with rfl | ⟨reset,rfl⟩ <;> rfl
    · rcases shape with rfl | ⟨reset,rfl⟩ <;> rfl
    · rcases shape with rfl | ⟨reset,rfl⟩
      · simp only [same,ite_false]
      · cases endpoint : p.endpoint <;> simp [peerFixedAttrs,clearedSource,endpoint,same]


end Leanux.Proofs.WG.Config
