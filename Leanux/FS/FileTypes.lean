import Leanux.FS.EventfdTypes

namespace Leanux.FS

structure FDEntry where
  objectId : Nat
  cloexec : Bool
  deriving Repr, BEq, DecidableEq

structure File where
  ctx : Eventfd.Ctx
  statusFlags : UInt32
  deriving Repr, BEq, DecidableEq

/-- Slots 0–7 are permanently occupied by the fixture, outside fdTable.
    Objects with no live descriptors remain inaccessible historical cells;
    this abstracts allocation reclamation, not descriptor ownership. -/
structure Files where
  fdTable : Nat → Option FDEntry
  objects : Nat → Option File
  nextObject : Nat
  nextFd : Nat
  limit : Nat

def initialFiles : Files :=
  ⟨fun _ => none, fun _ => none, 0, 8, 32⟩

def lookupDescriptor (s : Files) (fd : Nat) : Option FDEntry := s.fdTable fd

def lookupFile (s : Files) (fd : Nat) : Option File :=
  (lookupDescriptor s fd).bind fun d => s.objects d.objectId

/-- The admitted finite table and object references, including cursor safety. -/
def WellFormed (s : Files) : Prop :=
  s.limit = 32 ∧ 8 ≤ s.nextFd ∧ s.nextFd ≤ s.limit ∧
  (∀ fd d, s.fdTable fd = some d → 8 ≤ fd ∧ fd < s.limit ∧
    d.objectId < s.nextObject ∧ ∃ f, s.objects d.objectId = some f) ∧
  (∀ fd, 8 ≤ fd → fd < s.nextFd → ∃ d, s.fdTable fd = some d)

end Leanux.FS
