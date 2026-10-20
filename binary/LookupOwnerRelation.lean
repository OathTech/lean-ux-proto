import OwnerPending
import LookupPeerRelation

namespace Binary.LookupRelation
open Leanux Leanux.WG LookupObservation

/-- A write to the selected owner preserves the bucket and count equations.
    Its current/pending owner clause is supplied by the actual store phase. -/
theorem Physical.frame_owner (c : Config) (raw raw' : List MachineState)
    (seen seen' : List Point) (s t : MachineState) (v : View)
    (represented : Physical c raw seen s v) (owner : IndexOwner)
    (focused : c.focus.owner = some owner) (word : Option PeerId)
    (inactive : helperActive seen = false) (inactive' : helperActive seen' = false)
    (writes : Address → Prop) (same : EqualOutside writes s.data.dmem t.data.dmem)
    (bucketApart : ∀ a, TrustBase.LookupBucketBytes c v a → ¬writes a)
    (countApart : ∀ a, TrustBase.LookupCountBytes c a → ¬writes a)
    (ownerAt : OwnerFieldAt c seen' t owner word) :
    Physical c raw' seen' t {v with ownerWord := some word} := by
  obtain ⟨selection, ⟨head, loaded, bucket⟩, oldOwner, count⟩ := represented
  refine ⟨selection, ⟨head, ?_, ?_⟩, ?_, ?_⟩
  · exact (same.loadInt _ 8 (fun i hi => bucketApart _ (.inl ⟨i, hi, rfl⟩))).symm.trans loaded
  · apply BucketShape.frame_reads same _ _ head bucket
    intro cell member address read
    obtain ⟨e, memberE, eq⟩ := List.mem_map.mp member
    subst cell
    exact bucketApart address (.inr ⟨e, memberE, read⟩)
  · simp only [focused]
    exact ⟨word, rfl, ownerAt⟩
  · cases peer : c.focus.peer with
    | none => simpa only [peer] using count
    | some id =>
      simp only [peer] at count ⊢
      obtain ⟨n, value, nonnull, field⟩ := count
      refine ⟨n, value, nonnull, ?_⟩
      simp only [countPhase, inactive, inactive', Bool.false_eq_true, ite_false, PeerCountPhase.At] at field ⊢
      exact (same.loadInt _ 4 (fun i hi => countApart _ ⟨id, peer, i, hi, rfl⟩)).symm.trans field

/-- The pending owner equation reads the old word from the actual helper
    return, and the new word from the actual store. No peer liveness premise. -/
theorem owner_pending_result (c : Config) (seen : List Point) (s : MachineData)
    (owner : IndexOwner) (word : Option PeerId)
    (returned : lastHelperReturn seen = some ⟨s, Image.Lookup.entry+0xba⟩)
    (location : s.regs.rbx.toBitVec = ownerAddress c owner)
    (field : OwnerWord.Field c.peers s.dmem (ownerAddress c owner) word)
    (af : Bool) (q : MachineState) (member : q ∈ LookupHistory.resultStates s af)
    (pending : OwnerWord.PendingPC q.pc) :
    OwnerFieldAt c seen q owner word := by
  have phase : ownerPending seen q = some ⟨s, Image.Lookup.entry+0xba⟩ := by
    simp only [ownerPending, OwnerWord.PendingPC] at pending ⊢
    rw [ite_eq_left pending, returned]
  simp only [OwnerFieldAt, phase]
  refine ⟨True.intro, location, field, ?_⟩
  rw [← location, LookupHistory.resultStates_memory s af q member]
  exact load64_store _ _ _

/-- At the decision successor the physical owner word has the returned
    value, including NULL. The source setter is related separately. -/
theorem owner_committed_result (c : Config) (seen : List Point) (s : MachineData)
    (owner : IndexOwner) (word : Option PeerId)
    (location : s.regs.rbx.toBitVec = ownerAddress c owner)
    (result : s.regs.rax.toBitVec = OwnerWord.pointer c.peers word)
    (af : Bool) :
    OwnerFieldAt c seen (LookupHistory.resultExit s af) owner word := by
  have phase : ownerPending seen (LookupHistory.resultExit s af) = none := by
    simp [ownerPending, LookupHistory.resultExit, Image.Lookup.entry]
    split <;> rw [ite_eq_right (by decide)]
  simp only [OwnerFieldAt, phase]
  change OwnerWord.Field c.peers (OwnerWord.stored s).dmem (ownerAddress c owner) word
  rw [← location]
  exact OwnerWord.stored_field _ _ _ result

#print axioms Physical.frame_owner
#print axioms owner_pending_result
#print axioms owner_committed_result
end Binary.LookupRelation
