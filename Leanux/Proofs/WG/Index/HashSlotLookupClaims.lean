import Leanux.Proofs.WG.Index.HashSlotLookupSource
import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceLookupHeldClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceTableSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Actual lookup keeps the new coverage invariant together with positive
hashed-owner coherence. Null/zero-owner misses are excluded by the entry
coherence; ordinary misses and all original Stops retain their semantics. -/
theorem indexLookup_hashSlots (kinds : List IndexKind) (index : Nat) :
    Campaign2.Ensures (indexLookup kinds index)
      (fun s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s)
      (fun _ s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s) := by
  intro g ambient result out after pre run
  refine ⟨indexLookup_owner_coherent_safe kinds index g ambient result out after pre.1 run,?_⟩
  intro final present
  cases device : g.dev with
  | none =>
    have unchanged := indexLookup_cursor kinds index (g.dev.map TimerDiscipline.tableCursor)
      g ambient result out after rfl run
    have absent : out.dev = none := by simpa [device] using unchanged
    change out.dev = some final at present
    rw [absent] at present
    cases present
  | some d =>
    obtain ⟨actual,output,coverage⟩ := indexLookup_hashSlots_device kinds index d
      (pre.1 d device) (pre.2 d device) g ambient result out after device run
    rw [present] at output
    cases output
    exact coverage

theorem indexRemove_hashSlots (owner : IndexOwner) (d : Device)
    (covered : HashSlotCoverage d) :
    Campaign2.Returns (liftIndex (indexRemove owner)) (fun s => s.wg.device = some d)
      (fun _ s =>
        s.wg.device = some {d with indexTable := removeOwner owner d.indexTable} ∧
        HashSlotCoverage {d with indexTable := removeOwner owner d.indexTable}) := by
  intro g ambient device
  obtain ⟨value,final,after,run,effect⟩ := indexRemove_exact owner d g ambient device
  exact ⟨value,final,after,run,effect,hashSlotCoverage_remove d owner covered⟩

/-- A returned keypair index selects a resident key in one of its owner's
actual slots. The acquired peer reference and positive key reference come
from the same original lookup; this is still a supplied-invariant contract. -/
theorem indexLookup_keypair_slot_held (index : Nat) :
    Campaign2.Ensures (indexLookup [.keypair] index)
      (fun s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s)
      (fun result s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s ∧
        ∀ owner pid, result = some (owner,pid) → ∃ kid d p key,
          owner = .keypair kid ∧ s.wg.device = some d ∧
          d.peers[pid]? = some p ∧ 1 < p.refcount ∧
          d.keypairs[kid]? = some key ∧ key.peer = some pid ∧
          0 < key.refcount ∧ some kid ∈ clearKeys p) := by
  intro g ambient result out after pre run
  have invariants := indexLookup_hashSlots [.keypair] index g ambient result out after pre run
  refine ⟨invariants.1,invariants.2,?_⟩
  intro owner pid returned
  obtain ⟨kid,d,p,key,own,device,peer,count,stored,word,positive⟩ :=
    (indexLookup_keypair_held index g ambient result out after pre.1 run).2 owner pid returned
  cases initial : g.dev with
  | none =>
    rw [indexLookup_factor] at run
    simp [lookupPrefix,liftIndex,getDev,initial,invariant,AmbientM.invariant] at run
    cases run
  | some before =>
    obtain ⟨found,_,_,q,resident,_,_,effect⟩ :=
      indexLookup_success [.keypair] index before g ambient result out after initial run owner pid returned
    have table : d.indexTable = before.indexTable := by
      have same := Option.some.inj (device.symm.trans effect)
      rw [same]
      cases owner <;> simp only [writeOwnerWord] <;> split <;> rfl
    have member : {index,owner := IndexOwner.keypair kid} ∈ d.indexTable := by
      rw [table]
      simpa only [own] using List.mem_of_find?_eq_some found
    obtain ⟨target,other,k,otherPeer,otherKey,otherWord,slot⟩ :=
      invariants.2 d device _ member kid rfl
    have sameKey : k = key := Option.some.inj (otherKey.symm.trans stored)
    subst k
    have samePid : target = pid := Option.some.inj (otherWord.symm.trans word)
    subst target
    have samePeer : other = p := Option.some.inj (otherPeer.symm.trans peer)
    subst other
    exact ⟨kid,d,p,key,own,device,peer,count,stored,word,positive,slot⟩

end Leanux.Proofs.WG.Index
