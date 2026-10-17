import Leanux.Proofs.WG.Index.LookupMiss
/-! Success inversion for the original index lookup. Residency and the reference
bounds are conclusions of the actual returning run, not coherence premises. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

/-- A successful suffix read and reference acquisition expose the original owner
word and positively referenced peer. No isDead condition is inferred. -/
theorem lookupFinish_success_pre (index : Nat) (owner : IndexOwner) (d : Device) :
    Ensures (lookupFinish (some {index, owner}, true)) (fun g => g.dev = some d)
      (fun ret _ => ∀ own pid, ret = some (own, pid) →
        own = owner ∧ ownerWord d owner = some (some pid) ∧ ∃ p,
          d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2 ^ 31) := by
  intro g ambient result final after device run own pid returned
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
  | none =>
    obtain ⟨actual, endState, endAmbient, actualRun, isNone, _⟩ :=
      lookupFinish_null index owner d residentWord g ambient device
    have impossible := (valueEq actual endState endAmbient actualRun).trans isNone
    simp [returned] at impossible
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
      · obtain ⟨actual, endState, endAmbient, actualRun, isNone, _⟩ :=
          lookupFinish_dead index owner d target p residentWord resident zero g ambient device
        have impossible := (valueEq actual endState endAmbient actualRun).trans isNone
        simp [returned] at impossible
      · have positive : 0 < p.refcount := by omega
        by_cases bounded : p.refcount + 1 < 2 ^ 31
        · obtain ⟨actual, endState, endAmbient, actualRun, isSome, _⟩ :=
            lookupFinish_live index owner d target p residentWord resident positive bounded g ambient device
          have values := returned.symm.trans ((valueEq actual endState endAmbient actualRun).trans isSome)
          simp only [Option.some.injEq, Prod.mk.injEq] at values
          rcases values with ⟨rfl, rfl⟩
          exact ⟨rfl, residentWord, p, resident, positive, bounded⟩
        · have overflow : 2147483647 ≤ p.refcount := by omega
          exact False.elim (stops (some target) residentWord
            (.outsideDomain s!"{Decision.refcountAddNzWraps.info.file}:{Decision.refcountAddNzWraps.info.line}"
              "refcount_warn_saturate (overflow)") (by
              intro middle next device
              simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, device, resident,
                refcountIncNotZero, zero, overflow, branch, AmbientM.branch, branchCmp,
                AmbientM.branchCmp, unsupported, AmbientM.unsupported]
              rfl))


/-- The exact successful suffix effect follows from the derived entry facts and
the existing total effect on that same concrete run; owner/peer aliases remain. -/
theorem lookupFinish_success (index : Nat) (owner : IndexOwner) (d : Device) :
    Ensures (lookupFinish (some {index, owner}, true)) (fun g => g.dev = some d)
      (fun ret g => ∀ own pid, ret = some (own, pid) →
        own = owner ∧ ownerWord d owner = some (some pid) ∧ ∃ p,
          d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2 ^ 31 ∧
          g.dev = some (writeOwnerWord (acquirePeer d pid p) owner (some pid))) := by
  intro g ambient ret final after pre run own pid returned
  obtain ⟨same, word, p, resident, live, bounded⟩ :=
    lookupFinish_success_pre index owner d g ambient ret final after pre run own pid returned
  obtain ⟨result, endState, endAmbient, actual, value, device⟩ :=
    lookupFinish_live index owner d pid p word resident live bounded g ambient pre
  rw [run] at actual
  obtain ⟨pair, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
  exact ⟨same, word, p, resident, live, bounded, device⟩

/-- Successful original lookup selects the first equal numeric index, whose kind
must be permitted, and performs exactly the acquired-peer/owner-word writes. -/
theorem indexLookup_success (kinds : List IndexKind) (index : Nat) (d : Device) :
    Ensures (indexLookup kinds index) (fun g => g.dev = some d)
      (fun result final => ∀ owner pid, result = some (owner, pid) →
        d.indexTable.find? (·.index == index) = some {index, owner} ∧
        kinds.contains (IndexEntry.kind {index, owner}) = true ∧
        ownerWord d owner = some (some pid) ∧ ∃ p,
          d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2 ^ 31 ∧
          final.dev = some (writeOwnerWord (acquirePeer d pid p) owner (some pid))) := by
  intro entry ambient result final after device run owner pid returned
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
    obtain ⟨result', final', after', actual, value, unchanged⟩ :=
      indexLookup_miss kinds index d miss entry ambient device
    rw [run] at actual
    obtain ⟨pair, rfl⟩ := Prod.mk.inj (Except.ok.inj actual)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    simp_all
  obtain ⟨⟨number, own⟩, found, permitted⟩ := matched
  have numeric : number = index := by simpa using List.find?_some found
  subst number
  obtain ⟨state, middle, next, prefixRun, stateEq, middleDevice⟩ :=
    lookupPrefix_matching kinds index own d found permitted entry ambient device
  rw [indexLookup_factor] at run
  change (((lookupPrefix kinds index).run entry).run ambient >>= fun ((s, m), a) =>
    ((lookupFinish s).run m).run a) = _ at run
  rw [prefixRun] at run
  subst state
  obtain ⟨same, word, p, resident, positive, bounded, effect⟩ :=
    lookupFinish_success index own d middle next result final after middleDevice run owner pid returned
  subst owner
  exact ⟨found, permitted, word, p, resident, positive, bounded, effect⟩

end Leanux.Proofs.WG.Index
