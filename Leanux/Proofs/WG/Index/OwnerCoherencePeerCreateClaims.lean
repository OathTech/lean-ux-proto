import Leanux.Proofs.WG.Index.OwnerCoherencePeerCreateSource
import Leanux.Proofs.WG.Index.OwnerCoherenceCreatorModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Peer creation preserves local hashed-owner coherence on every normal
result. Every returned peer has the actual initialized self-word and unit
reference count, even when the allocation cursor overwrites a resident peer. -/
theorem peerCreate_owner_coherent (publicKey : Key) (psk : Option Key) :
    Campaign2.Ensures (peerCreate publicKey psk) View.OwnerCoherentSafe
      (fun result s => View.OwnerCoherentSafe s ∧
        ∀pid, result = .ok pid → ∃d p,
          s.wg.device = some d ∧ d.peers[pid]? = some p ∧
          p.refcount = 1 ∧ p.handshakeEntryPeer = some pid) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [peerCreate, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    have effect := peerCreate_owner_fields publicKey psk d g ambient result final after device run
    cases result with
    | error code =>
      refine ⟨?_,by intro pid impossible; cases impossible⟩
      intro current present
      have same : current = d := Option.some.inj (present.symm.trans effect)
      subst current
      exact pre d device
    | ok pid =>
      obtain ⟨current,p,present,footprint,resident,unit,self⟩ := effect
      refine ⟨?_,?_⟩
      · intro actual actualDevice
        have same : actual = current := Option.some.inj (actualDevice.symm.trans present)
        subst actual
        exact peerCreateFootprint_owner_coherent d current pid p footprint resident
          (by omega) self (pre d device)
      · intro target same
        cases same
        exact ⟨current,p,present,resident,unit,self⟩

/-- The returned initialization facts establish the creators' explicit
publisher premise, without requiring a fresh peer cursor. -/
theorem peerCreate_handshake_publisher (publicKey : Key) (psk : Option Key) :
    Campaign2.Ensures (peerCreate publicKey psk) View.OwnerCoherentSafe
      (fun result s => View.OwnerCoherentSafe s ∧
        ∀pid, result = .ok pid → View.HandshakePublisherSafe pid s) := by
  intro g ambient result final after pre run
  obtain ⟨safe,created⟩ := peerCreate_owner_coherent publicKey psk
    g ambient result final after pre run
  refine ⟨safe,?_⟩
  intro pid returned d device
  obtain ⟨current,p,present,resident,unit,self⟩ := created pid returned
  have same : current = d := Option.some.inj (present.symm.trans device)
  subst current
  refine ⟨safe d device,pid,p,?_,resident,by omega,rfl⟩
  simp [ownerWord, resident, self]

end Leanux.Proofs.WG.Index
