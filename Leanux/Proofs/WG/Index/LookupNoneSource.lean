import Leanux.Proofs.WG.Index.LookupProvenanceSource
import Leanux.Proofs.WG.Index.LookupNoneModel

/-! Empty-result inversion of the original lookup, including its actual stores.
No table uniqueness, owner coherence, readiness or isDead premise is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

theorem lookupFinish_none_pre (index : Nat) (owner : IndexOwner) (d : Device) :
    Ensures (lookupFinish (some { index, owner }, true)) (fun g => g.dev = some d)
      (fun ret _ => ret = none →
        ownerWord d owner = some none ∨ ∃ pid p,
          ownerWord d owner = some (some pid) ∧ d.peers[pid]? = some p ∧
          p.refcount = 0) := by
  intro g ambient result final after device run returned
  have present : ∃ word, ownerWord d owner = some word := by
    cases word : ownerWord d owner with
    | some value => exact ⟨value, rfl⟩
    | none =>
      exfalso
      cases owner with
      | handshake id =>
        cases hp : d.peers[id]? with
        | some p => simp [ownerWord, hp] at word
        | none =>
          simp [lookupFinish, IndexOwner.peerWord, getPeer, getDev, device, hp,
            branch, AmbientM.branch, invariant, AmbientM.invariant] at run
          cases run
      | keypair id =>
        cases hk : d.keypairs[id]? with
        | some k => simp [ownerWord, hk] at word
        | none =>
          simp [lookupFinish, IndexOwner.peerWord, getKeypair, getDev, device, hk,
            branch, AmbientM.branch, invariant, AmbientM.invariant] at run
          cases run
  have valueEq (actual : Option (IndexOwner × PeerId)) (endState : WGWorld)
      (endAmbient : Ambient)
      (actualRun : ((lookupFinish (some {index, owner}, true)).run g).run ambient =
        .ok ((actual, endState), endAmbient)) : result = actual :=
    congrArg (fun out : ((Option (IndexOwner × PeerId) × WGWorld) × Ambient) => out.1.1)
      (Except.ok.inj (run.symm.trans actualRun))
  have stops (word : Option PeerId) (resident : ownerWord d owner = some word) (stop : Stop)
      (bad : ∀ middle next, middle.dev = some d →
        ((peerGetMaybeZero word).run middle).run next = .error stop) : False := by
    let start := recordStep ambient .idxFound true
    obtain ⟨value, middle, next, readRun, valueWord, readDevice⟩ :=
      peerWord_returns owner d word resident g start device
    rw [valueWord] at readRun
    dsimp only [start, recordStep] at readRun
    have badRun := bad middle next readDevice
    simp [lookupFinish, branch, AmbientM.branch, StateT.run_bind, readRun, badRun] at run
    cases run
  obtain ⟨word, residentWord⟩ := present
  cases word with
  | none => exact Or.inl residentWord
  | some target =>
    cases resident : d.peers[target]? with
    | none =>
      exact False.elim (stops (some target) residentWord (.invariant s!"dangling peer {target}") (by
        intro middle next device
        simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, device, resident,
          branch, AmbientM.branch, invariant, AmbientM.invariant]
        rfl))
    | some p =>
      by_cases zero : p.refcount = 0
      · exact Or.inr ⟨target, p, residentWord, resident, zero⟩
      · have positive : 0 < p.refcount := by omega
        by_cases bounded : p.refcount + 1 < 2 ^ 31
        · obtain ⟨actual, endState, endAmbient, actualRun, isSome, _⟩ :=
            lookupFinish_live index owner d target p residentWord resident positive bounded g ambient device
          have impossible := (valueEq actual endState endAmbient actualRun).trans isSome
          simp [returned] at impossible
        · have overflow : 2147483647 ≤ p.refcount := by omega
          exact False.elim (stops (some target) residentWord
            (.outsideDomain s!"{Decision.refcountAddNzWraps.info.file}:{Decision.refcountAddNzWraps.info.line}"
              "refcount_warn_saturate (overflow)") (by
              intro middle next device
              simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, device, resident,
                refcountIncNotZero, zero, overflow, branch, AmbientM.branch, branchCmp,
                AmbientM.branchCmp, unsupported, AmbientM.unsupported]
              rfl))

/-- Every normal empty result has exactly one cause and its exact final device.
The two permitted-entry cases both retain the original owner-word clear. -/
theorem indexLookup_none (kinds : List IndexKind) (index : Nat) (d : Device) :
    Ensures (indexLookup kinds index) (fun g => g.dev = some d)
      (fun result final => result = none → ∃ d', final.dev = some d' ∧
        ∃ cause, LookupNoneCase kinds index d d' cause ∧
          ∀ other, LookupNoneCase kinds index d d' other → other = cause) := by
  intro entry ambient result final after device run returned
  by_cases matched : ∃ e, d.indexTable.find? (·.index == index) = some e ∧
      kinds.contains e.kind = true
  · obtain ⟨⟨number, owner⟩, found, permitted⟩ := matched
    have numeric : number = index := by simpa using List.find?_some found
    subst number
    obtain ⟨state, middle, next, prefixRun, stateEq, middleDevice⟩ :=
      lookupPrefix_matching kinds index owner d found permitted entry ambient device
    have suffixRun := run
    rw [indexLookup_factor] at suffixRun
    change (((lookupPrefix kinds index).run entry).run ambient >>= fun ((s, m), a) =>
      ((lookupFinish s).run m).run a) = _ at suffixRun
    rw [prefixRun] at suffixRun
    subst state
    have reasons := lookupFinish_none_pre index owner d middle next result final after
      middleDevice suffixRun returned
    rcases reasons with word | ⟨pid, p, word, resident, zero⟩
    · obtain ⟨result', final', after', actual, value, effect⟩ :=
        indexLookup_null kinds index owner d found permitted word entry ambient device
      rw [run] at actual
      obtain ⟨pair, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
      have facts : LookupNoneCase kinds index d (writeOwnerWord d owner none)
          .nullOwnerWord := ⟨owner, found, permitted, word, rfl⟩
      exact ⟨_, effect, .nullOwnerWord, facts,
        fun other h => lookupNoneCase_unique kinds index d _ other _ h facts⟩
    · obtain ⟨result', final', after', actual, value, effect⟩ :=
        indexLookup_dead kinds index owner d found permitted pid p word resident zero entry ambient device
      rw [run] at actual
      obtain ⟨pair, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
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
    obtain ⟨result', final', after', actual, value, effect⟩ :=
      indexLookup_miss kinds index d miss entry ambient device
    rw [run] at actual
    obtain ⟨pair, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    have facts : LookupNoneCase kinds index d d .absentOrDisallowed := ⟨miss, rfl⟩
    exact ⟨d, effect, .absentOrDisallowed, facts,
      fun other h => lookupNoneCase_unique kinds index d d other _ h facts⟩

end Leanux.Proofs.WG.Index
