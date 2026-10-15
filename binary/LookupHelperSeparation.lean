import LookupHelperStack
import PeerStartHistory

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory

/-- Internal helper obligations derived from the original lookup allocation
    discipline. This is a proved preparation record, not an entry premise. -/
structure HelperSeparation (c : Config) (coverage : LookupCoverage.Context) (helper : MachineData) : Prop where
  push : ∀ a, coverage.bytes a → ¬InRange (helper.regs.rsp.toBitVec-56) 56 a
  stack : coverage.Separated (InRange (helper.regs.rsp.toBitVec-56) 64)
  metadata : coverage.Separated coverage.metadataBytes
  preempt : coverage.Separated (InRange preemptCountAddress 4)
  reads : ∀ a, Reads c coverage.entryView a → ¬PeerGet.entryWrites helper coverage a
  count : ∀ pid, c.focus.peer = some pid → ∀ a,
    InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a →
    ¬(InRange (helper.regs.rsp.toBitVec-56) 64 a ∨ coverage.writes a)
  countService : ∀ pid, c.focus.peer = some pid →
    (∃ n, coverage.entryView.count = some n ∧ n ≠ 0) →
    ∀ a, coverage.bytes a → ¬InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a
  bucket : ∀ a, LookupBucketBytes c coverage.entryView a → ¬LookupDataWrites c coverage.entryView a
  ownerCount : ∀ a, LookupCountBytes c a → ¬LookupOwnerBytes c a

theorem helper_separation_from_entry (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (returnAddress : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (helper : MachineData) (stack : helper.regs.rsp = s.regs.rsp-48) :
    HelperSeparation c ⟨coverage, preempt, v⟩ helper := by
  have words : LookupStackWords c = 13 := by simp [LookupStackWords, focused]
  have base : helper.regs.rsp.toBitVec-56 = s.regs.rsp.toBitVec-104 := by
    rw [stack, UInt64.toBitVec_sub, BitVec.sub_sub]
    rfl
  have inWrites : ∀ a, InRange (helper.regs.rsp.toBitVec-56) 64 a →
      LookupStackWrites c ⟨s, Image.Lookup.entry⟩ a := by
    intro a inside
    unfold LookupStackWrites
    rw [words]
    obtain ⟨j, hj, eq⟩ := inside
    exact ⟨j, by omega, by simpa only [base, show BitVec.ofNat 64 (8*13) = 104 from rfl] using eq⟩
  have inLive : ∀ a, InRange (helper.regs.rsp.toBitVec-56) 64 a →
      LookupLiveStack c ⟨s, Image.Lookup.entry⟩ a := by
    intro a inside
    unfold LookupLiveStack
    rw [words]
    obtain ⟨j, hj, eq⟩ := inside
    exact ⟨j, by omega, by simpa only [base, show BitVec.ofNat 64 (8*13) = 104 from rfl] using eq⟩
  have scratch : ∀ a, InRange (helper.regs.rsp.toBitVec-56) 56 a →
      LookupStackWrites c ⟨s, Image.Lookup.entry⟩ a := by
    intro a inside
    apply inWrites a
    obtain ⟨j, hj, eq⟩ := inside
    exact ⟨j, by omega, eq⟩
  refine ⟨?_, ?_, entry.coverageMetadata, entry.coveragePreempt, ?_, ?_, ?_, entry.dataBucket, entry.ownerCount⟩
  · intro a service written
    exact entry.serviceStack a service (scratch a written)
  · intro a covered inside
    exact entry.coverageStack a covered (inLive a inside)
  · intro a read written
    apply entry.readsScratch a read
    rcases written with stack | buffer
    · exact .inl (scratch a stack)
    · exact .inr (.inl buffer)
  · intro pid peer a counted written
    apply entry.readsScratch a (.inr (.inr (.inr ⟨pid, peer, counted⟩)))
    rcases written with stack | buffer
    · exact .inl (inWrites a stack)
    · exact .inr (.inl buffer)
  · intro pid peer live a service counted
    exact entry.dataService a service (.inr ⟨live, pid, peer, counted⟩)

#print axioms helper_separation_from_entry
end Binary.LookupRelation
