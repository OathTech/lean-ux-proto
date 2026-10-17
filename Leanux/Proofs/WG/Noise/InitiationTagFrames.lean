import Leanux.Proofs.WG.Noise.ResponseTagFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Local variant of Keypairs.Frames.WGBase.pubkeyLookup_spec. The actual
acquisition preserves every optional tag and supplies a retained reference. -/
theorem pubkeyLookup_spec_initiationTagMap_variant (key : Key) (entry : Option Device) :
    Ensures (pubkeyLookup key)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun result g => responseTagMap g.dev = responseTagMap entry ∧
        ∀pid, result = some pid → ResponseTagHeld entry pid g) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [pubkeyLookup, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases found : d.peerHashtable.find? (·.1 == key) with
    | none =>
      simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
        branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact ⟨pre, by intro pid impossible; cases impossible⟩
    | some pair =>
      obtain ⟨tableKey,pid⟩ := pair
      cases resident : d.peers[pid]? with
      | none =>
        simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
          requireNotPending, getPeer, resident, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
            requireNotPending, getPeer, resident, refcountIncNotZero, zero,
            branch, branchCmp, AmbientM.branch, AmbientM.branchCmp] at run
          rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
          exact ⟨pre, by intro target impossible; cases impossible⟩
        · by_cases overflow : 2147483647 ≤ p.refcount
          · simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
              requireNotPending, getPeer, resident, refcountIncNotZero, zero,
              overflow, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
              unsupported, AmbientM.unsupported] at run
            cases run
          · simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
              requireNotPending, getPeer, resident, refcountIncNotZero, zero,
              overflow, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
              setPeer, modifyDev] at run
            rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
            have same : responseTagMap (some (Index.acquirePeer d pid p)) =
                responseTagMap entry :=
              (tagMap_write d pid p {p with refcount := p.refcount + 1} resident rfl).trans
                (by simpa [device] using pre)
            refine ⟨same, ?_⟩
            intro target equal
            cases equal
            exact ⟨same, Index.acquirePeer d pid p, {p with refcount := p.refcount + 1},
              rfl, by simp [Index.acquirePeer], by change 1 < p.refcount + 1; omega⟩

/-- Local read/write variant of Keypairs.Frames.WGTransitions.modifyPeer_spec for
all tags and the reference actually held by this consumer. -/
theorem modifyPeer_spec_initiationTagMap_variant (entry : Option Device) (pid : PeerId)
    (f : Peer → Peer) (tag : ∀p, (f p).handshakeState = p.handshakeState)
    (count : ∀p, (f p).refcount = p.refcount) :
    Ensures (modifyPeer pid f) (ResponseTagHeld entry pid)
      (fun _ => ResponseTagHeld entry pid) := by
  intro g ambient result final after pre run
  obtain ⟨same,d,p,device,resident,retained⟩ := pre
  change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
  simp [getPeer, getDev, device, resident, setPeer, modifyDev] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  refine ⟨?_,_,f p,rfl,by simp,?_⟩
  · exact (tagMap_write d pid p (f p) resident (tag p)).trans (by simpa [device] using same)
  · simpa only [count] using retained

end Leanux.Proofs.WG.Noise
