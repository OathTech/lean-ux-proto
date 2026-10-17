import Leanux.Proofs.WG.Noise.ResponseTagModel
import Leanux.Proofs.WG.Index.OwnerCoherenceFrames
import Leanux.Proofs.WG.Index.LookupNoneSource
import Leanux.Proofs.WG.Config.PeerScalars

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

def ResponseTagHeld (entry : Option Device) (pid : PeerId) (g : WGWorld) : Prop :=
  responseTagMap g.dev = responseTagMap entry ∧
    ∃d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount

private theorem tagMap_write (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]? = some p) (tag : q.handshakeState = p.handshakeState) :
    responseTagMap (some {d with peers := d.peers.insert pid q}) = responseTagMap (some d) := by
  funext other
  by_cases same : pid = other
  · subst other; simp [responseTagMap, resident, tag]
  · simp [responseTagMap, Std.TreeMap.getElem?_insert, same]

private theorem tagMap_owner (d : Device) (owner : IndexOwner) (word : Option PeerId) :
    responseTagMap (some (Index.writeOwnerWord d owner word)) = responseTagMap (some d) := by
  cases owner with
  | keypair id => cases found : d.keypairs[id]? <;> simp only [Index.writeOwnerWord, found] <;> rfl
  | handshake pid =>
    cases found : d.peers[pid]? with
    | none => simp [Index.writeOwnerWord, found]
    | some p => simp only [Index.writeOwnerWord, found]; exact tagMap_write d pid p _ found rfl

/-- Local variant of Keypairs.Frames.WGBase.indexLookup_spec. Normal lookup
preserves all optional handshake tags and supplies its actual held reference;
owner/reference aliasing and failed-owner clears remain. -/
theorem indexLookup_spec_responseTagMap_variant (kinds : List IndexKind) (index : Nat) (entry : Option Device) :
    Ensures (indexLookup kinds index) (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun out g => responseTagMap g.dev = responseTagMap entry ∧
        ∀owner pid, out = some (owner,pid) → ∃d p,
          g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount) := by
  intro g ambient out final after pre run
  cases device : g.dev with
  | none =>
    rw [Index.indexLookup_factor] at run
    simp [Index.lookupPrefix, liftIndex, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases out with
    | none =>
      obtain ⟨next,effect,cause,facts,_⟩ :=
        Index.indexLookup_none kinds index d g ambient none final after device run rfl
      have same : responseTagMap (some next) = responseTagMap (some d) := by
        cases cause with
        | absentOrDisallowed => exact congrArg (fun x => responseTagMap (some x)) facts.2
        | nullOwnerWord =>
          obtain ⟨owner,_,_,_,rfl⟩ := facts
          exact tagMap_owner d owner none
        | zeroReference =>
          obtain ⟨owner,_,_,_,_,_,_,_,rfl⟩ := facts
          exact tagMap_owner d owner none
      refine ⟨?_, ?_⟩
      · rw [effect, same]; simpa [device] using pre
      · intro owner pid impossible; cases impossible
    | some pair =>
      obtain ⟨owner,pid⟩ := pair
      obtain ⟨_,_,word,p,resident,positive,_,effect⟩ :=
        Index.indexLookup_success kinds index d g ambient (some (owner,pid)) final after device run owner pid rfl
      have acquiredWord := Index.acquirePeer_word d pid p owner (some pid) resident word
      have unchanged := Index.writeOwnerWord_same_peers (Index.acquirePeer d pid p) owner (some pid) acquiredWord
      refine ⟨?_, ?_⟩
      · rw [effect, tagMap_owner]
        have same := tagMap_write d pid p {p with refcount := p.refcount + 1} resident rfl
        change responseTagMap (some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}}) = _
        rw [same]; simpa [device] using pre
      · intro own target returned
        cases returned
        refine ⟨_,{p with refcount := p.refcount + 1},effect,?_,by change 1 < p.refcount + 1; omega⟩
        rw [unchanged]
        simp [Index.acquirePeer]

/-- Local variant of Keypairs.Frames.WGBase.peerPut_spec. Rejection releases
the actual held reference, so no peer is removed. -/
theorem peerPut_spec_responseTagMap_variant (entry : Option Device) (pid : PeerId) :
    Ensures (peerPut (some pid)) (ResponseTagHeld entry pid)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  obtain ⟨same,d,p,device,resident,retained⟩ := pre
  have effect := ((ensures_iff _ _ _).mpr (Config.peerPut_retained pid d p resident retained))
    g ambient result final after device run
  rw [effect]
  exact (tagMap_write d pid p {p with refcount := p.refcount-1} resident rfl).trans (by simpa [device] using same)


end Leanux.Proofs.WG.Noise
