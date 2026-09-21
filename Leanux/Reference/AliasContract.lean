import Leanux.FS.File

namespace Leanux.Reference

/-- Fixed obligation over the actual executable descriptor-close helper.
The entire surviving file value is preserved, including its context and status
flags. Unreachable historical objects need not be reclaimed by this model. -/
def CloseAliasPreservation : Prop :=
  ∀ (s : Leanux.FS.Files) (closed other : Nat)
      (a b : Leanux.FS.FDEntry) (file : Leanux.FS.File),
    Leanux.FS.WellFormed s →
    closed ≠ other →
    Leanux.FS.lookupDescriptor s closed = some a →
    Leanux.FS.lookupDescriptor s other = some b →
    a.objectId = b.objectId →
    Leanux.FS.lookupFile s other = some file →
    ∃ after,
      Leanux.FS.fileCloseFd s closed = some (a, after) ∧
      Leanux.FS.lookupDescriptor after closed = none ∧
      Leanux.FS.lookupDescriptor after other = some b ∧
      Leanux.FS.lookupFile after other = some file ∧
      after.objects b.objectId = some file

end Leanux.Reference
