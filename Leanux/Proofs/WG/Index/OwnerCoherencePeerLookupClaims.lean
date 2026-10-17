import Leanux.Proofs.WG.Index.OwnerCoherenceClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Every successful index lookup carries the actual newly acquired peer
reference. The mask and owner kind are arbitrary; normal failure retains
coherence, without any added reference budget or readiness premise. -/
theorem indexLookup_peer_held (kinds : List IndexKind) (index : Nat) :
    Campaign2.Ensures (indexLookup kinds index) View.OwnerCoherentSafe
      (fun result s => View.OwnerCoherentSafe s ∧
        ∀ owner pid, result = some (owner, pid) → ∃ d p,
          s.wg.device = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount) := by
  intro g ambient result out after pre run
  refine ⟨indexLookup_owner_coherent_safe kinds index g ambient result out after pre run, ?_⟩
  intro owner pid returned
  cases device : g.dev with
  | none =>
    rw [indexLookup_factor] at run
    simp [lookupPrefix, liftIndex, getDev, device,
      invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨_, _, word, p, resident, positive, _, effect⟩ :=
      indexLookup_success kinds index d g ambient result out after device run owner pid returned
    have acquiredWord := acquirePeer_word d pid p owner (some pid) resident word
    refine ⟨writeOwnerWord (acquirePeer d pid p) owner (some pid),
      {p with refcount := p.refcount + 1}, effect, ?_, ?_⟩
    · rw [writeOwnerWord_same_peers _ _ _ acquiredWord]
      simp [acquirePeer]
    · change 1 < p.refcount + 1
      omega

end Leanux.Proofs.WG.Index
