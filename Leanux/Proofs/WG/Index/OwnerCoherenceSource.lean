import Leanux.Proofs.WG.Index.OwnerCoherenceFrames
import Leanux.Proofs.WG.Index.LookupNoneSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Every normally returning lookup preserves hashed-owner coherence. The
actual increment and owner-word store are retained; overflow and all other
stopped outcomes are outside this partial contract. -/
theorem indexLookup_owner_coherence (kinds : List IndexKind) (index : Nat) (d : Device)
    (coherent : HashedOwnersCoherent d) :
    Campaign2.Ensures (indexLookup kinds index) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧ HashedOwnersCoherent final) := by
  intro g ambient result out after device run
  cases result with
  | none =>
    obtain ⟨final, present, cause, facts, _⟩ :=
      indexLookup_none kinds index d g ambient none out after device run rfl
    cases cause with
    | absentOrDisallowed =>
      obtain ⟨_, rfl⟩ := facts
      exact ⟨_, present, coherent⟩
    | nullOwnerWord =>
      obtain ⟨owner, found, _, null, _⟩ := facts
      obtain ⟨pid, p, word, _, _, _⟩ := coherent {index, owner} (List.mem_of_find?_eq_some found)
      simp [word] at null
    | zeroReference =>
      obtain ⟨owner, pid, p, found, _, word, resident, zero, _⟩ := facts
      obtain ⟨target, q, expected, stored, positive, _⟩ :=
        coherent {index, owner} (List.mem_of_find?_eq_some found)
      have same : target = pid := Option.some.inj (Option.some.inj (expected.symm.trans word))
      subst target
      have samePeer : q = p := Option.some.inj (stored.symm.trans resident)
      subst q
      omega
  | some pair =>
    obtain ⟨owner, pid⟩ := pair
    obtain ⟨_, _, word, p, resident, _, _, effect⟩ :=
      indexLookup_success kinds index d g ambient (some (owner, pid)) out after device run owner pid rfl
    refine ⟨writeOwnerWord (acquirePeer d pid p) owner (some pid), effect, ?_⟩
    intro e member
    have table : (writeOwnerWord (acquirePeer d pid p) owner (some pid)).indexTable = d.indexTable := by
      have unchanged (before : Device) (writer : IndexOwner) (word : Option PeerId) :
          (writeOwnerWord before writer word).indexTable = before.indexTable := by
        cases writer <;> simp only [writeOwnerWord] <;> split <;> rfl
      exact (unchanged (acquirePeer d pid p) owner (some pid)).trans rfl
    rw [table] at member
    exact ownerCoherent_write_same _ owner e.owner (some pid)
      (acquirePeer_word d pid p owner (some pid) resident word)
      (ownerCoherent_acquire d pid p resident e.owner (coherent e member))

end Leanux.Proofs.WG.Index
