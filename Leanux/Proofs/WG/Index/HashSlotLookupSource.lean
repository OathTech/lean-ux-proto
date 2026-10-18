import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceLookupHeldClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceTableSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

theorem indexLookup_hashSlots_device (kinds : List IndexKind) (index : Nat) (d : Device)
    (coherent : HashedOwnersCoherent d) (covered : HashSlotCoverage d) :
    Campaign2.Ensures (indexLookup kinds index) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧ HashSlotCoverage final) := by
  intro g ambient result out after device run
  cases result with
  | none =>
    obtain ⟨final,present,cause,facts,_⟩ :=
      indexLookup_none kinds index d g ambient none out after device run rfl
    cases cause with
    | absentOrDisallowed =>
      obtain ⟨_,rfl⟩ := facts
      exact ⟨_,present,covered⟩
    | nullOwnerWord =>
      obtain ⟨owner,found,_,null,_⟩ := facts
      obtain ⟨pid,p,word,_,_,_⟩ := coherent {index,owner} (List.mem_of_find?_eq_some found)
      simp [word] at null
    | zeroReference =>
      obtain ⟨owner,pid,p,found,_,word,resident,zero,_⟩ := facts
      obtain ⟨target,q,expected,stored,positive,_⟩ :=
        coherent {index,owner} (List.mem_of_find?_eq_some found)
      have same : target = pid := Option.some.inj (Option.some.inj (expected.symm.trans word))
      subst target
      have samePeer : q = p := Option.some.inj (stored.symm.trans resident)
      subst q
      omega
  | some pair =>
    obtain ⟨owner,pid⟩ := pair
    obtain ⟨_,_,word,p,resident,_,_,effect⟩ :=
      indexLookup_success kinds index d g ambient (some (owner,pid)) out after device run owner pid rfl
    exact ⟨_,effect,hashSlotCoverage_write_same _ owner (some pid)
      (acquirePeer_word d pid p owner (some pid) resident word)
      (hashSlotCoverage_acquire d pid p resident covered)⟩

end Leanux.Proofs.WG.Index
