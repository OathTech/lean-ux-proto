import Leanux.Proofs.WG.Index.LookupProvenanceSource
import Leanux.Proofs.WG.Index.LookupNoneModel

/-! Empty-result inversion of the original lookup, including its actual stores.
No table uniqueness, owner coherence, readiness or isDead premise is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

theorem lookupFinish_none_pre (index : Nat) (owner : IndexOwner) (d : Device) :
    Ensures (lookupFinish (some { index, owner }, true)) (fun w => w.k.wg = some d)
      (fun ret _ => ret = none →
        ownerWord d owner = some none ∨ ∃ pid p,
          ownerWord d owner = some (some pid) ∧ d.peers[pid]? = some p ∧
          p.refcount = 0) := by
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

/-- Every normal empty result has exactly one cause and its exact final device.
The two permitted-entry cases both retain the original owner-word clear. -/
theorem indexLookup_none (kinds : List IndexKind) (index : Nat) (d : Device) :
    Ensures (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result final => result = none → ∃ d', final.k.wg = some d' ∧
        ∃ cause, LookupNoneCase kinds index d d' cause ∧
          ∀ other, LookupNoneCase kinds index d d' other → other = cause) := by
  intro entry result final device run returned
  by_cases matched : ∃ e, d.indexTable.find? (·.index == index) = some e ∧
      kinds.contains e.kind = true
  · obtain ⟨⟨number, owner⟩, found, permitted⟩ := matched
    have numeric : number = index := by simpa using List.find?_some found
    subst number
    obtain ⟨state, middle, prefixRun, stateEq, middleDevice⟩ :=
      lookupPrefix_matching kinds index owner d found permitted entry device
    have suffixRun := run
    rw [indexLookup_factor, StateT.run_bind, prefixRun] at suffixRun
    subst state
    have reasons := lookupFinish_none_pre index owner d middle result final
      middleDevice suffixRun returned
    rcases reasons with word | ⟨pid, p, word, resident, zero⟩
    · obtain ⟨result', final', actual, value, effect⟩ :=
        indexLookup_null kinds index owner d found permitted word entry device
      rw [run] at actual
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
      have facts : LookupNoneCase kinds index d (writeOwnerWord d owner none)
          .nullOwnerWord := ⟨owner, found, permitted, word, rfl⟩
      exact ⟨_, effect, .nullOwnerWord, facts,
        fun other h => lookupNoneCase_unique kinds index d _ other _ h facts⟩
    · obtain ⟨result', final', actual, value, effect⟩ :=
        indexLookup_dead kinds index owner d found permitted pid p word resident zero entry device
      rw [run] at actual
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
      have facts : LookupNoneCase kinds index d (writeOwnerWord d owner none)
          .zeroReference := ⟨owner, pid, p, found, permitted, word, resident, zero, rfl⟩
      exact ⟨_, effect, .zeroReference, facts,
        fun other h => lookupNoneCase_unique kinds index d _ other _ h facts⟩
  · have miss : ∀ e, d.indexTable.find? (·.index == index) = some e →
        kinds.contains e.kind = false := by
      intro e found
      cases h : kinds.contains e.kind
      · rfl
      · exact False.elim (matched ⟨e, found, h⟩)
    obtain ⟨result', final', actual, value, effect⟩ :=
      indexLookup_miss kinds index d miss entry device
    rw [run] at actual
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
    have facts : LookupNoneCase kinds index d d .absentOrDisallowed := ⟨miss, rfl⟩
    exact ⟨d, effect, .absentOrDisallowed, facts,
      fun other h => lookupNoneCase_unique kinds index d d other _ h facts⟩

end Leanux.Proofs.WG.Index
