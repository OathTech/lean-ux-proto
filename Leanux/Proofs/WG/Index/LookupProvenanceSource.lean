import Leanux.Proofs.WG.Index.LookupMiss
/-! Success inversion for the original index lookup. Residency and the reference
bounds are conclusions of the actual returning run, not coherence premises. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

/-- A successful suffix read and reference acquisition expose the original owner
word and positively referenced peer. No isDead condition is inferred. -/
theorem lookupFinish_success_pre (index : Nat) (owner : IndexOwner) (d : Device) :
    Ensures (lookupFinish (some { index, owner }, true)) (fun w => w.k.wg = some d)
      (fun ret _ => ∀ own pid, ret = some (own, pid) →
        own = owner ∧ ownerWord d owner = some (some pid) ∧ ∃ p,
          d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2 ^ 31) := by
  rw [ensures_iff]
  cases owner <;>
    mvcgen [lookupFinish, IndexOwner.peerWord, IndexOwner.setPeerWord,
      peerGetMaybeZero, requireNotPending, refcountIncNotZero, getPeer, getKeypair,
      getDev, getK, setPeer, setKeypair, modifyDev, modifyK, branch, branchCmp,
      invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [ownerWord]
  all_goals grind

/-- The exact successful suffix effect follows from the derived entry facts and
the existing total effect on that same concrete run; owner/peer aliases remain. -/
theorem lookupFinish_success (index : Nat) (owner : IndexOwner) (d : Device) :
    Ensures (lookupFinish (some { index, owner }, true)) (fun w => w.k.wg = some d)
      (fun ret w => ∀ own pid, ret = some (own, pid) →
        own = owner ∧ ownerWord d owner = some (some pid) ∧ ∃ p,
          d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2 ^ 31 ∧
          w.k.wg = some (writeOwnerWord (acquirePeer d pid p) owner (some pid))) := by
  intro w ret final pre run own pid returned
  obtain ⟨same, word, p, resident, live, bounded⟩ :=
    lookupFinish_success_pre index owner d w ret final pre run own pid returned
  obtain ⟨result, after, actual, value, device⟩ :=
    lookupFinish_live index owner d pid p word resident live bounded w pre
  rw [run] at actual
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
  exact ⟨same, word, p, resident, live, bounded, device⟩
/-- Successful original lookup selects the first equal numeric index, whose kind
must be permitted, and performs exactly the acquired-peer/owner-word writes. -/
theorem indexLookup_success (kinds : List IndexKind) (index : Nat) (d : Device) :
    Ensures (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result final => ∀ owner pid, result = some (owner, pid) →
        d.indexTable.find? (·.index == index) = some { index, owner } ∧
        kinds.contains (IndexEntry.kind { index, owner }) = true ∧
        ownerWord d owner = some (some pid) ∧ ∃ p,
          d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2 ^ 31 ∧
          final.k.wg = some (writeOwnerWord (acquirePeer d pid p) owner (some pid))) := by
  intro entry result final device run owner pid returned
  have matched : ∃ e, d.indexTable.find? (·.index == index) = some e ∧
      kinds.contains e.kind = true := by
    apply Classical.byContradiction
    intro no
    have miss : ∀ e, d.indexTable.find? (·.index == index) = some e →
        kinds.contains e.kind = false := by
      intro e found
      cases h : kinds.contains e.kind
      · rfl
      · exact False.elim (no ⟨e, found, h⟩)
    obtain ⟨result', final', actual, value, unchanged⟩ :=
      indexLookup_miss kinds index d miss entry device
    rw [run] at actual
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
    simp_all
  obtain ⟨⟨number, own⟩, found, permitted⟩ := matched
  have numeric : number = index := by simpa using List.find?_some found
  subst number
  obtain ⟨state, middle, prefixRun, stateEq, middleDevice⟩ :=
    lookupPrefix_matching kinds index own d found permitted entry device
  rw [indexLookup_factor, StateT.run_bind, prefixRun] at run
  subst state
  obtain ⟨same, word, p, resident, positive, bounded, effect⟩ :=
    lookupFinish_success index own d middle result final middleDevice run owner pid returned
  subst owner
  exact ⟨found, permitted, word, p, resident, positive, bounded, effect⟩

end Leanux.Proofs.WG.Index
