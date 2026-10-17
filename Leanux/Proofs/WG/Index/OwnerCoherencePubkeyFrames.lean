import Leanux.Proofs.WG.Index.OwnerCoherenceHeldFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Actual public-key lookup preserves hashed owners on misses and zero-count
returns, and supplies the held reference on every successful lookup. -/
theorem pubkeyLookup_owner_held (key : Key) :
    Ensures (pubkeyLookup key)
      (fun g => ∀d, g.dev = some d → HashedOwnersCoherent d)
      (fun result g => (∀d, g.dev = some d → HashedOwnersCoherent d) ∧
        ∀pid, result = some pid → OwnerPeerHeldWG pid g) := by
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
            have coherent : HashedOwnersCoherent (acquirePeer d pid p) := by
              intro e member
              exact ownerCoherent_acquire d pid p resident e.owner (pre d device e member)
            have safe : ∀ actual,
                some (acquirePeer d pid p) = some actual → HashedOwnersCoherent actual := by
              intro actual same; cases same; exact coherent
            refine ⟨safe, ?_⟩
            intro target same
            cases same
            exact ⟨safe, acquirePeer d pid p, {p with refcount := p.refcount + 1},
              rfl, by simp [acquirePeer], by simp; omega⟩

end Leanux.Proofs.WG.Index
