import Leanux.Proofs.WG.Index.OwnerCoherencePeerCreateModel
import Leanux.Proofs.WG.Noise.SlotFrames
import Leanux.Proofs.WG.Config.Precomputation

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Internal initialization state. In particular `word = none` does not
assert coherence of an overwritten handshake owner during initialization. -/
def PeerCreateAt (before : Device) (pid : PeerId) (word : Option PeerId)
    (g : WGWorld) : Prop :=
  ∃ current p, g.dev = some current ∧ PeerCreateFootprint before current pid ∧
    current.peers[pid]? = some p ∧ p.refcount = 1 ∧ p.handshakeEntryPeer = word

/-- Replacing a possibly aliased peer by a positive self-owner restores every
hashed owner's coherence. Counts and ownership of references are not equated. -/
theorem peerCreateFootprint_owner_coherent (before after : Device) (pid : PeerId)
    (p : Peer) (footprint : PeerCreateFootprint before after pid)
    (resident : after.peers[pid]? = some p) (positive : 0 < p.refcount)
    (self : p.handshakeEntryPeer = some pid) (coherent : HashedOwnersCoherent before) :
    HashedOwnersCoherent after := by
  intro e member
  obtain ⟨target,q,word,found,live,owned⟩ := coherent e (footprint.1 ▸ member)
  by_cases alias : target = pid
  · subst target
    refine ⟨pid,p,?_,resident,positive,?_⟩
    · cases owner : e.owner with
      | handshake own =>
        have same : pid = own := by simpa only [owner] using owned
        subst own
        simp [ownerWord, resident, self]
      | keypair key => simpa [ownerWord, owner, footprint.2.1] using word
    · cases owner : e.owner with
      | handshake own => simpa only [owner] using owned
      | keypair key => simpa only [owner, footprint.2.1] using owned
  · refine ⟨target,q,?_,(footprint.2.2 target alias).trans found,live,?_⟩
    · cases owner : e.owner with
      | handshake own =>
        have same : target = own := by simpa only [owner] using owned
        subst own
        simpa only [ownerWord, owner, footprint.2.2 target alias] using word
      | keypair key => simpa [ownerWord, owner, footprint.2.1] using word
    · cases owner : e.owner with
      | handshake own => simpa only [owner] using owned
      | keypair key => simpa only [owner, footprint.2.1] using owned

/-- An actual field update preserves the initialization footprint and unit
reference count, while explicitly allowing the initialization of its word. -/
theorem modifyPeer_createAt (before : Device) (pid : PeerId)
    (oldWord newWord : Option PeerId) (f : Peer → Peer)
    (word : ∀p, p.handshakeEntryPeer = oldWord → (f p).handshakeEntryPeer = newWord)
    (count : ∀p, (f p).refcount = p.refcount) :
    Ensures (modifyPeer pid f) (PeerCreateAt before pid oldWord)
      (fun _ => PeerCreateAt before pid newWord) := by
  intro g ambient result final after pre run
  obtain ⟨current,p,device,footprint,resident,unit,old⟩ := pre
  change (((do let q ← getPeer pid; setPeer pid (f q)) : WG.M Unit).run g).run ambient = _ at run
  simp [getPeer, getDev, device, resident, setPeer, modifyDev] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  refine ⟨{current with peers := current.peers.insert pid (f p)},f p,rfl,?_,by simp,?_,word p old⟩
  · refine ⟨footprint.1,footprint.2.1,?_⟩
    intro other different
    simpa [Std.TreeMap.getElem?_insert, Ne.symm different] using footprint.2.2 other different
  · simpa [count] using unit

theorem precompute_createAt (before : Device) (pid : PeerId) (word : Option PeerId) :
    Ensures (precomputeStaticStatic pid) (PeerCreateAt before pid word)
      (fun _ => PeerCreateAt before pid word) := by
  intro g ambient result final after pre run
  obtain ⟨current,p,device,footprint,resident,unit,old⟩ := pre
  obtain ⟨value,out,tail,execution,effect⟩ :=
    Config.precomputeStaticStatic_returns pid current p resident g ambient device
  rw [run] at execution
  cases execution
  refine ⟨Config.precomputeDevice current pid p,
    {p with precomputedStaticStatic := Config.precomputedAfter current.staticIdentity p},
    effect,?_,Config.precomputeDevice_peer pid current p,unit,old⟩
  unfold Config.precomputeDevice
  split
  · dsimp only
    split
    · refine ⟨footprint.1,footprint.2.1,?_⟩
      intro other different
      simpa [Config.withPeer, Std.TreeMap.getElem?_insert, Ne.symm different] using footprint.2.2 other different
    · refine ⟨footprint.1,footprint.2.1,?_⟩
      intro other different
      simpa [Config.withPeer, Std.TreeMap.getElem?_insert, Ne.symm different] using footprint.2.2 other different
  · refine ⟨footprint.1,footprint.2.1,?_⟩
    intro other different
    simpa [Config.withPeer, Std.TreeMap.getElem?_insert, Ne.symm different] using footprint.2.2 other different

end Leanux.Proofs.WG.Index
