import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceLookupHeldClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceTableSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

theorem indexLookup_preserves_coherent_source (kinds : List IndexKind) (index : Nat)
    (D : Device → Prop)
    (acquired : ∀ d pid p, d.peers[pid]?=some p → D d → D (acquirePeer d pid p))
    (stored : ∀ d owner word, ownerWord d owner=some word → D d → D (writeOwnerWord d owner word))
    (d : Device) (coherent : HashedOwnersCoherent d) (safe : D d) :
    Campaign2.Ensures (indexLookup kinds index) (fun s => s.wg.device=some d)
      (fun _ s => ∃ final,s.wg.device=some final ∧ D final) := by
  intro g ambient result out after device run
  cases result with
  | none =>
    obtain ⟨final,present,cause,facts,_⟩ :=
      indexLookup_none kinds index d g ambient none out after device run rfl
    cases cause with
    | absentOrDisallowed =>
      obtain ⟨_,rfl⟩ := facts
      exact ⟨_,present,safe⟩
    | nullOwnerWord =>
      obtain ⟨owner,found,_,null,_⟩ := facts
      obtain ⟨pid,p,word,_,_,_⟩ := coherent {index,owner} (List.mem_of_find?_eq_some found)
      simp [word] at null
    | zeroReference =>
      obtain ⟨owner,pid,p,found,_,word,resident,zero,_⟩ := facts
      obtain ⟨target,q,expected,foundPeer,positive,_⟩ :=
        coherent {index,owner} (List.mem_of_find?_eq_some found)
      have same : target=pid := Option.some.inj (Option.some.inj (expected.symm.trans word))
      subst target
      have samePeer : q=p := Option.some.inj (foundPeer.symm.trans resident)
      subst q
      omega
  | some pair =>
    obtain ⟨owner,pid⟩ := pair
    obtain ⟨_,_,word,p,resident,_,_,effect⟩ :=
      indexLookup_success kinds index d g ambient (some (owner,pid)) out after device run owner pid rfl
    exact ⟨_,effect,stored _ owner (some pid)
      (acquirePeer_word d pid p owner (some pid) resident word)
      (acquired d pid p resident safe)⟩

theorem indexLookup_hashSlots_device (kinds : List IndexKind) (index : Nat) (d : Device)
    (coherent : HashedOwnersCoherent d) (covered : HashSlotCoverage d) :
    Campaign2.Ensures (indexLookup kinds index) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧ HashSlotCoverage final) :=
  indexLookup_preserves_coherent_source kinds index HashSlotCoverage
    hashSlotCoverage_acquire hashSlotCoverage_write_same d coherent covered

end Leanux.Proofs.WG.Index
