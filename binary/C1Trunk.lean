import C1Interfaces
import C1TrunkRootBody
import C1TrunkNodeNoMem
import C1TrunkExact
import C1TrunkChild

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

/-- PACKAGE 2. Empty root, the node installed. `FramedHolds` is not used. -/
theorem pathRoot : PathRoot := by
  intro below _ alloc fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
    inv ready _ facts hcase
  have rf := C1Trunk.insertReady_facts ready
  obtain ⟨bound,empty,okHead,stEq⟩ := C1Trunk.step_root (d := d) (family := family)
    (key := key) (cidr := cidr) (pid := pid) (placed := placed) (exact := exact)
    (outcomes := stream.map fun r => r.bytes.head? == some 1) (by rw [← facts.model]; exact hcase)
  have answerEq : answer = 0 := by rw [facts.result, facts.model, stEq]
  have after := facts.after
  have sites := facts.sites
  have outcomes := facts.outcomes
  have recordsAfter := facts.recordsAfter
  rw [facts.model, stEq] at after sites outcomes recordsAfter
  obtain ⟨record,rest,pending⟩ : ∃ record rest, stream = record :: rest := by
    cases stream with
    | nil => simp [Case.sites] at sites
    | cons record rest => exact ⟨record,rest,rfl⟩
  subst pending
  have recordSite : record.site = 77 := by simpa [Case.sites] using sites
  have ok : record.bytes.head? = some 1 := by
    rcases outcomes record (by simp) with h | h
    · simp [h] at okHead
    · exact h
  have recordsAfter' : w'.ambient.hidden = some rest := by simpa using recordsAfter
  obtain ⟨d',device',same⟩ := after
  rw [answerEq]
  rcases rf.families with rfl | rfl
  · exact C1Trunk.through_core fetch L A premises c s w w' true key cidr pid ra 0 inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = record :: rest := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact C1Trunk.root_body below alloc premises ready trunk bound empty record rest rfl
          recordSite ok ⟨d',device',fun owner hasPeer => same.trans
            (congrArg Allowedips.target (C1Trunk.root_device (bump d0) true key cidr pid owner hasPeer))⟩
          recordsAfter' facts.armedAfter)
  · exact C1Trunk.through_core fetch L A premises c s w w' false key cidr pid ra 0 inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = record :: rest := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact C1Trunk.root_body below alloc premises ready trunk bound empty record rest rfl
          recordSite ok ⟨d',device',fun owner hasPeer => same.trans
            (congrArg Allowedips.target (C1Trunk.root_device (bump d0) false key cidr pid owner hasPeer))⟩
          recordsAfter' facts.armedAfter)

/-- PACKAGE 2. Nonempty root, no exact match, the allocation at :205 refused. -/
theorem pathNodeNoMem : PathNodeNoMem := by
  intro framed alloc fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
    inv ready _ facts hcase
  have rf := C1Trunk.insertReady_facts ready
  have hcase' : (step d family key cidr pid placed exact
      (stream.map fun r => r.bytes.head? == some 1)).case = .nodeNoMem := by
    rw [← facts.model]; exact hcase
  obtain ⟨notExact,failedHead,stEq⟩ := C1Trunk.step_nodeNoMem hcase'
  obtain ⟨bound,rootId,rootAt⟩ := C1Trunk.step_walked_of (.inr (.inl hcase'))
  subst notExact
  have answerEq : answer = -ENOMEM := by rw [facts.result, facts.model, stEq]
  have after : ∃ d', w'.wg.dev = some d' ∧ Allowedips.target d' = Allowedips.target (bump d) := by
    have h := facts.after
    rw [facts.model, stEq] at h
    exact h
  have sites := facts.sites
  have outcomes := facts.outcomes
  have recordsAfter := facts.recordsAfter
  rw [facts.model, stEq] at sites outcomes recordsAfter
  obtain ⟨record,rest,pending,recordSite⟩ := C1Trunk.first_site sites
  subst pending
  have failed : record.bytes.head? = some 0 := by
    rcases outcomes record (by simp) with h | h
    · exact h
    · exact absurd (by simp [h]) failedHead
  have recordsAfter' : w'.ambient.hidden = some rest := by simpa using recordsAfter
  obtain ⟨⟨ambient,finalAmbient,finalStore,accepted⟩,_⟩ := facts.walked
    (by rw [hcase]; decide) (by rw [hcase]; decide) (by rw [hcase]; decide)
  have rootNode := C1Trunk.ordered_root facts.trie rootAt
  rw [answerEq]
  rcases rf.families with rfl | rfl
  · exact C1Trunk.to_trunk fetch L A premises c s w true key cidr pid ra inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame _
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = record :: rest := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact C1Trunk.nodeNoMem_body framed alloc premises ready trunk bound facts.keyBound rootId rootAt
          rootNode placed ambient finalAmbient finalStore
          (by rw [show rootOf d0 4 = some rootId from rootAt] at accepted; exact accepted)
          record rest rfl recordSite failed after recordsAfter' facts.armedAfter)
  · exact C1Trunk.to_trunk fetch L A premises c s w false key cidr pid ra inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame _
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = record :: rest := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact C1Trunk.nodeNoMem_body framed alloc premises ready trunk bound facts.keyBound rootId rootAt
          rootNode placed ambient finalAmbient finalStore
          (by rw [show rootOf d0 6 = some rootId from rootAt] at accepted; exact accepted)
          record rest rfl recordSite failed after recordsAfter' facts.armedAfter)

/-- PACKAGE 2. Exact match: the placed node's peer is replaced. -/
theorem pathExact : PathExact := C1Trunk.pathExact_proof

/-- PACKAGE 2. Child attachment, from `C1Trunk.StackOffPeers`. NOT the
interface's `PathChild` alone: the landed child theorem takes the landed
`NodeInit.boundary`, which needs the stack apart from whole peer objects
(see `C1TrunkCut`). -/
theorem pathChild_of_stackOffPeers : C1Trunk.StackOffPeers → PathChild := by
  intro off below framed alloc fetch L A premises c s w w' family key cidr pid ra answer d stream placed
    exact st inv ready _ facts hcase
  have rf := C1Trunk.insertReady_facts ready
  have hcase' : (step d family key cidr pid placed exact
      (stream.map fun r => r.bytes.head? == some 1)).case = .child := by
    rw [← facts.model]; exact hcase
  obtain ⟨notExact,okHead,rootId,rootAt,nothing,stEq⟩ := C1Trunk.step_child hcase'
  obtain ⟨bound,_⟩ := C1Trunk.step_walked_of (.inr (.inr (.inl hcase')))
  subst notExact
  obtain ⟨⟨ambient,finalAmbient,finalStore,accepted⟩,walkFact⟩ := facts.walked
    (by rw [hcase]; decide) (by rw [hcase]; decide) (by rw [hcase]; decide)
  have rootNode := C1Trunk.ordered_root facts.trie rootAt
  have peersOff := off L A c s family key cidr pid ra ready
  cases placed with
  | none =>
    obtain ⟨node,hasRoot,_⟩ := rootNode
    exact absurd nothing (C1Trunk.child_placed hasRoot)
  | some p =>
    obtain ⟨pn,hasParent,width,short,exactIff,prefixEq⟩ := C1Trunk.walk_placed walkFact
    have measure : pn.cidr < cidr :=
      Nat.lt_of_le_of_ne short (fun h => Bool.false_ne_true (exactIff.mpr h))
    have empty := C1Trunk.child_empty (d0 := bump d) facts.trie hasParent nothing
    have answerEq : answer = 0 := by rw [facts.result, facts.model, stEq]
    have after := facts.after
    have sites := facts.sites
    have recordsAfter := facts.recordsAfter
    rw [facts.model, stEq] at after sites recordsAfter
    obtain ⟨record,rest,pending,recordSite⟩ := C1Trunk.first_site sites
    subst pending
    have ok : record.bytes.head? = some 1 := by simpa using okHead
    have recordsAfter' : w'.ambient.hidden = some rest := by simpa using recordsAfter
    rw [answerEq]
    rcases rf.families with rfl | rfl
    · exact C1Trunk.to_trunk fetch L A premises c s w true key cidr pid ra inv
        rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame _
        (fun names stream0 d0 seq a trunk => by
          have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
          have hs : stream0 = record :: rest := Option.some.inj (trunk.hidden.symm.trans facts.records)
          subst hd hs
          exact C1Trunk.child_body below framed alloc premises ready trunk peersOff bound facts.keyBound
            rootId rootAt rootNode p pn hasParent width measure (by rw [width]; exact prefixEq) empty
            ambient finalAmbient finalStore
            (by rw [show rootOf d0 4 = some rootId from rootAt] at accepted; exact accepted)
            record rest rfl recordSite ok after recordsAfter' facts.armedAfter)
    · exact C1Trunk.to_trunk fetch L A premises c s w false key cidr pid ra inv
        rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame _
        (fun names stream0 d0 seq a trunk => by
          have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
          have hs : stream0 = record :: rest := Option.some.inj (trunk.hidden.symm.trans facts.records)
          subst hd hs
          exact C1Trunk.child_body below framed alloc premises ready trunk peersOff bound facts.keyBound
            rootId rootAt rootNode p pn hasParent width measure (by rw [width]; exact prefixEq) empty
            ambient finalAmbient finalStore
            (by rw [show rootOf d0 6 = some rootId from rootAt] at accepted; exact accepted)
            record rest rfl recordSite ok after recordsAfter' facts.armedAfter)

/-- PACKAGE 2, for package 3: the trunk in the strengthened form package 3's
paths take (`TrunkToNodePlus`, in `C1Cut`).
NOT the interface's `TrunkHolds`: `C1Trunk.StackOffPeers` is an extra
hypothesis, not derivable from the signed text (see `C1TrunkCut`). -/
theorem trunkToNodePlus_of_stackOffPeers :
    C1Trunk.StackOffPeers → NodeBelowTop → FramedHolds → AllocRule → TrunkToNodePlus :=
  C1Trunk.trunkToNodePlus

/-- PACKAGE 2, for package 3: `TrunkHolds` from `C1Trunk.StackOffPeers`. -/
theorem trunkHolds_of_stackOffPeers : C1Trunk.StackOffPeers → TrunkHolds :=
  fun off below framed alloc => trunk_of_plus (C1Trunk.trunkToNodePlus off below framed alloc)

#print axioms pathTooLong
#print axioms pathRootNoMem
#print axioms pathRoot
#print axioms pathNodeNoMem
#print axioms pathExact
#print axioms pathChild_of_stackOffPeers
#print axioms trunkToNodePlus_of_stackOffPeers
#print axioms trunkHolds_of_stackOffPeers
end Binary.Statements.C1.Proof
