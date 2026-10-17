import Leanux.Proofs.WG.Index.OwnerCoherenceSessionFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseClaims
import Leanux.Proofs.WG.Noise.SlotFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- The native frame invariant for an actual held reference. This is internal
caller state; public preservation claims remain over the campaign projection. -/
def OwnerPeerHeldWG (pid : PeerId) (g : WGWorld) : Prop :=
  (∀d, g.dev = some d → HashedOwnersCoherent d) ∧
    ∃d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount

/-- Actual resident-peer field writes retain local coherence and another
peer's held reference when owner words and counts are unchanged. Writer and
held peer may alias. Missing writers retain the original stopped path. -/
theorem modifyPeer_ownerHeld (focus writer : PeerId) (f : Peer → Peer)
    (word : ∀p, (f p).handshakeEntryPeer = p.handshakeEntryPeer)
    (count : ∀p, (f p).refcount = p.refcount) :
    Ensures (modifyPeer writer f) (OwnerPeerHeldWG focus)
      (fun _ => OwnerPeerHeldWG focus) := by
  intro g ambient result final after pre run
  obtain ⟨coherent,d,p,device,resident,retained⟩ := pre
  change (((do let q ← getPeer writer; setPeer writer (f q)) : WG.M Unit).run g).run ambient = _ at run
  cases found : d.peers[writer]? with
  | none =>
    simp [getPeer, getDev, device, found, invariant, AmbientM.invariant] at run
    cases run
  | some q =>
    simp [getPeer, getDev, device, found, setPeer, modifyDev] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    let next : Device := {d with peers := d.peers.insert writer (f q)}
    have nextCoherent := peerWrite_owner_coherent d writer q (f q) found
      (word q) (count q) (coherent d device)
    constructor
    · intro actual actualDevice
      change some next = some actual at actualDevice
      cases actualDevice
      exact nextCoherent
    · by_cases alias : writer = focus
      · subst focus
        have same : p = q := Option.some.inj (resident.symm.trans found)
        subst p
        exact ⟨next,f q,rfl,by simp [next],by rw [count]; exact retained⟩
      · exact ⟨next,p,rfl,by simpa [next, Std.TreeMap.getElem?_insert, alias] using resident,retained⟩

/-- Releasing the actual held reference is non-final. The last-owner
obligation is discharged from its count, not assumed of callers. -/
theorem peerPut_ownerHeld (pid : PeerId) :
    Ensures (peerPut (some pid)) (OwnerPeerHeldWG pid)
      (fun _ g => ∀d, g.dev = some d → HashedOwnersCoherent d) := by
  intro g ambient result final after pre run
  obtain ⟨coherent,d,p,device,resident,retained⟩ := pre
  exact peerPut_owner_coherent pid d p resident (by omega)
    (by intro last; omega) g ambient result final after ⟨device,coherent⟩ run

end Leanux.Proofs.WG.Index
