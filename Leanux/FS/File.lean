import Leanux.FS.FileTypes
import Leanux.FS.Eventfd

namespace Leanux.FS

def fdInstall (s : Files) (fd : Nat) (entry : FDEntry) : Files :=
  { s with fdTable := fun n => if n = fd then some entry else s.fdTable n }

def updateObject (s : Files) (objectId : Nat) (file : File) : Files :=
  { s with objects := fun n => if n = objectId then some file else s.objects n }

/-- file_close_fd_locked's table removal and __put_unused_fd cursor update. -/
def removeDescriptor (s : Files) (fd : Nat) : Files :=
  { s with
    fdTable := fun n => if n = fd then none else s.fdTable n
    nextFd := min fd s.nextFd }

/-- Actual close helper; a failed lookup leaves state untouched at the caller. -/
def fileCloseFd (s : Files) (fd : Nat) : Option (FDEntry × Files) :=
  match lookupDescriptor s fd with
  | none => none
  | some d => some (d, removeDescriptor s fd)

private def findUnused (s : Files) (start fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | remaining + 1 =>
    if start < 8 || (s.fdTable start).isSome then
      findUnused s (start + 1) remaining
    else some start

/-- alloc_fd(0, limit, flags): reserve the lowest free slot from next_fd.
    Installation is a separate helper, with no intervening operation in this
    sequential domain. Descriptor occupancy becomes observable at install. -/
def allocFd (s : Files) : Option (Nat × Files) :=
  match findUnused s s.nextFd (s.limit - s.nextFd) with
  | none => none
  | some fd => some (fd, { s with nextFd := fd + 1 })

/-- do_dup2 installs the shared file identity and descriptor-local flags.
    Replacing a live target releases its old logical ownership; historical
    object cells remain, and temporary kernel reference counts are abstracted. -/
def doDup2 (s : Files) (entry : FDEntry) (newfd : Nat) (cloexec : Bool) : Files :=
  fdInstall s newfd { entry with cloexec }

end Leanux.FS
