import PairInsertUnhashEntry

namespace Binary.Pair.Insert
open Leanux Leanux.WG Index

/-- Reconstructed data at a retry boundary, after the initial unlink. The
unlinked owner's index may contain an earlier rejected draw. -/
structure RetryData (n : Names) (o : Offsets) (m : DataMem)
    (d : Device) (owner : IndexOwner) (base : Nat) : Prop where
  related : Corresponds n o m d
  owned : Remove.ownership n o m=.ok (Remove.targetOwnership d)
  resident : Resident n o m owner base
  unlinked : word m "owner.pprev" (base+o.hash+o.pprev) 8=.ok 0

theorem RetryData.frame {n o before after d owner base}
    (ready : RetryData n o before d owner base) (frame : StorageFrame n o before after) :
    RetryData n o after d owner base := by
  have layout := (validate_basic (reconstruct_components ready.related).1).1
  refine ⟨frame.reconstruct ready.related,?_,ready.resident.frame layout frame,?_⟩
  · rw [←frame.ownership layout]
    exact ready.owned
  · have same := frame.word (entry_storage ready.resident.named) (o.hash+o.pprev) 8
      (by rw [layout.hash,layout.pprev,layout.entrySize]; omega) "owner.pprev"
    rw [←Nat.add_assoc] at same
    exact same.symm.trans ready.unlinked

def RetryData.entry {n o m d owner base} (ready : RetryData n o m d owner base) : UnlinkedEntry n o m :=
  ⟨owner,base,ready.resident.named,ready.unlinked⟩

def RetryPost (n : Names) (o : Offsets) (c : CommonBitsCoverage.Context) (initial : MachineState)
    (ra : UInt64) (d : Device) (owner : IndexOwner) (base : Nat) (t : MachineState) : Prop :=
  t.pc=codeEntry+0x6f ∧ Core n o c initial ra .outer t.data.dmem t.data ∧
    RetryData n o t.data.dmem d owner base

#print axioms RetryData.frame
end Binary.Pair.Insert
