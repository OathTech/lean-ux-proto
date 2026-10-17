import Leanux.Proofs.WG.Index.OwnerCoherenceClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- A returned keypair lookup carries the newly acquired peer reference and
the original positive key reference. Both are derived from this actual lookup
and entry coherence; no upper reference bound or readiness is assumed. -/
theorem indexLookup_keypair_held (index : Nat) :
    Campaign2.Ensures (indexLookup [.keypair] index) View.OwnerCoherentSafe
      (fun result s => View.OwnerCoherentSafe s ∧
        ∀ owner pid, result = some (owner, pid) → ∃ id d p k,
          owner = .keypair id ∧ s.wg.device = some d ∧
          d.peers[pid]? = some p ∧ 1 < p.refcount ∧
          d.keypairs[id]? = some k ∧ k.peer = some pid ∧ 0 < k.refcount) := by
  intro g ambient result out after pre run
  refine ⟨indexLookup_owner_coherent_safe [.keypair] index
    g ambient result out after pre run, ?_⟩
  intro owner pid returned
  cases device : g.dev with
  | none =>
    rw [indexLookup_factor] at run
    simp [lookupPrefix, liftIndex, getDev, device,
      invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨found, permitted, word, p, resident, positive, _, effect⟩ :=
      indexLookup_success [.keypair] index d g ambient result out after
        device run owner pid returned
    cases owner with
    | handshake own => cases permitted
    | keypair id =>
      obtain ⟨_, _, _, _, _, k, stored, live⟩ :=
        (pre d device) {index, owner := .keypair id} (List.mem_of_find?_eq_some found)
      have peerWord : k.peer = some pid := by
        simpa [ownerWord, stored] using word
      have acquiredWord := acquirePeer_word d pid p (.keypair id) (some pid) resident word
      let final := writeOwnerWord (acquirePeer d pid p) (.keypair id) (some pid)
      refine ⟨id, final, {p with refcount := p.refcount + 1}, k, rfl, effect, ?_, ?_, ?_, peerWord, live⟩
      · change (writeOwnerWord (acquirePeer d pid p) (.keypair id) (some pid)).peers[pid]? = _
        rw [writeOwnerWord_same_peers _ _ _ acquiredWord]
        simp [acquirePeer]
      · change 1 < p.refcount + 1
        omega
      · change (writeOwnerWord (acquirePeer d pid p) (.keypair id) (some pid)).keypairs[id]? = _
        rw [writeOwnerWord_same_keypairs _ _ _ acquiredWord]
        exact stored

end Leanux.Proofs.WG.Index
