import C1Interfaces
import C1TrunkFresh

/-! Result C1, work package 2: the trunk of the compiled insertion and the paths that end above the placement. This module is the package's root in
`binary/lakefile.toml`: add modules named `C1Trunk*.lean` and import them here.
The brief is `binary/Statements/C1/proof/WP2.md`. The acceptance theorems
are here; their parts are in the `C1Trunk*` modules. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- PACKAGE 2. The over-long prefix, both wrappers. `FramedHolds` is not
used: the wrapper's epilogue writes nothing, and `add`'s last callback is
carried by the landed frame lemmas and the contract's `frame` clause. -/
theorem pathTooLong : PathTooLong := by
  intro _ fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
    inv ready _ facts hcase
  have rf := C1Trunk.insertReady_facts ready
  obtain ⟨long,stEq⟩ := C1Trunk.step_tooLong (d := d) (family := family) (key := key) (cidr := cidr)
    (pid := pid) (placed := placed) (exact := exact)
    (outcomes := stream.map fun r => r.bytes.head? == some 1) (by rw [← facts.model]; exact hcase)
  have answerEq : answer = -EINVAL := by rw [facts.result, facts.model, stEq]
  have after : ∃ d', w'.wg.dev = some d' ∧ Allowedips.target d' = Allowedips.target (bump d) := by
    have h := facts.after
    rw [facts.model, stEq] at h
    exact h
  have recordsAfter : w'.ambient.hidden = some stream := by
    have h := facts.recordsAfter
    rw [facts.model, stEq] at h
    simpa using h
  rw [answerEq]
  rcases rf.families with rfl | rfl
  · exact C1Trunk.through_core fetch L A premises c s w w' true key cidr pid ra (-EINVAL) inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = stream := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact C1Trunk.tooLong_body fetch L A premises trunk long after recordsAfter facts.armedAfter)
  · exact C1Trunk.through_core fetch L A premises c s w w' false key cidr pid ra (-EINVAL) inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = stream := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact C1Trunk.tooLong_body fetch L A premises trunk long after recordsAfter facts.armedAfter)

/-- PACKAGE 2. Empty root, the allocation at :190 refused. `FramedHolds` is
not used. -/
theorem pathRootNoMem : PathRootNoMem := by
  intro _ alloc fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
    inv ready _ facts hcase
  have rf := C1Trunk.insertReady_facts ready
  obtain ⟨bound,empty,failedHead,stEq⟩ := C1Trunk.step_rootNoMem (d := d) (family := family)
    (key := key) (cidr := cidr) (pid := pid) (placed := placed) (exact := exact)
    (outcomes := stream.map fun r => r.bytes.head? == some 1) (by rw [← facts.model]; exact hcase)
  have answerEq : answer = -ENOMEM := by rw [facts.result, facts.model, stEq]
  have after : ∃ d', w'.wg.dev = some d' ∧ Allowedips.target d' = Allowedips.target (bump d) := by
    have h := facts.after
    rw [facts.model, stEq] at h
    exact h
  have sites := facts.sites
  have outcomes := facts.outcomes
  have recordsAfter := facts.recordsAfter
  rw [facts.model, stEq] at sites outcomes recordsAfter
  obtain ⟨record,rest,pending⟩ : ∃ record rest, stream = record :: rest := by
    cases stream with
    | nil => simp [Case.sites] at sites
    | cons record rest => exact ⟨record,rest,rfl⟩
  subst pending
  have recordSite : record.site = 77 := by simpa [Case.sites] using sites
  have failed : record.bytes.head? = some 0 := by
    rcases outcomes record (by simp) with h | h
    · exact h
    · exact absurd (by simp [h]) failedHead
  have recordsAfter' : w'.ambient.hidden = some rest := by simpa using recordsAfter
  rw [answerEq]
  rcases rf.families with rfl | rfl
  · exact C1Trunk.through_core fetch L A premises c s w w' true key cidr pid ra (-ENOMEM) inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = record :: rest := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact C1Trunk.rootNoMem_body alloc premises ready trunk bound empty record rest rfl
          recordSite failed after recordsAfter' facts.armedAfter)
  · exact C1Trunk.through_core fetch L A premises c s w w' false key cidr pid ra (-ENOMEM) inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = record :: rest := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact C1Trunk.rootNoMem_body alloc premises ready trunk bound empty record rest rfl
          recordSite failed after recordsAfter' facts.armedAfter)

#print axioms pathTooLong
#print axioms pathRootNoMem
end Binary.Statements.C1.Proof
