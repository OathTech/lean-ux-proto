import Leanux.Proofs.WG.HandshakeSecurity.RetentionFrames

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem RetainsHandshake.refl (w : WGWorld) : RetainsHandshake w w := fun _ _ h => h

theorem RetainsHandshake.trans (first : RetainsHandshake w v) (second : RetainsHandshake v u) :
    RetainsHandshake w u := fun pid view found => first pid view (second pid view found)

theorem peerGetMaybeZero_retains_handshake (peer : Option PeerId) (w v : WGWorld)
    (a b : Ambient) (result : Option PeerId)
    (run : ((peerGetMaybeZero peer).run w).run a = .ok ((result, v), b)) :
    RetainsHandshake w v := by
  cases peer with
  | none =>
    simp [peerGetMaybeZero, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact .refl _
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, hd, branch,
        AmbientM.branch, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, hd, hp,
          branch, AmbientM.branch, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0 <;> by_cases overflow : 2147483647 ≤ p.refcount <;>
          simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, setPeer, modifyDev,
            refcountIncNotZero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
            hd, hp, zero, overflow, unsupported, AmbientM.unsupported] at run
        all_goals try solve | cases run
        all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        all_goals first
          | exact .refl _
          | intro target view found
            by_cases same : pid = target
            · subst target
              simpa [peerView, hd, hp, handshakeView] using found
            · simpa [peerView, hd, Std.TreeMap.getElem?_insert, same] using found

theorem pubkeyLookup_retains_handshake (key : Key) (w v : WGWorld)
    (a b : Ambient) (result : Option PeerId)
    (run : ((pubkeyLookup key).run w).run a = .ok ((result, v), b)) :
    RetainsHandshake w v := by
  cases hd : w.dev with
  | none =>
    simp [pubkeyLookup, getDev, hd, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    have he : ((pubkeyLookup key).run w).run a =
        ((peerGetMaybeZero ((d.peerHashtable.find? (·.1 == key)).map (·.2))).run w).run
          (CounterWindow.record a .pubkeyLookupMatch
            ((d.peerHashtable.find? (·.1 == key)).map (·.2)).isSome) := by
      simp [pubkeyLookup, getDev, hd, branch, AmbientM.branch]
      rfl
    rw [he] at run
    exact peerGetMaybeZero_retains_handshake _ w v _ b result run

end Leanux.Proofs.WG.HandshakeSecurity
