import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionFileStores

/-! Original fdget/fdput and descriptor writes preserve suspended TX actors.
The final fput path queues task work using its actual task-state update; this
module does not yet cover execution of that queued work. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

theorem file_free (slot : FileId) : Keeps (fileFree slot) := by
  nested_suspension_source [fileFree] using [get_file,compare,unsupported,free_file]

theorem fput_reference (slot : FileId) : Keeps (fput slot) := by
  nested_suspension_source [fput] using [get_file,set_file,branch,file_free,get_task,modify_task,unsupported]

theorem lookup_fd (fd : Nat) : Keeps (filesLookupFdRaw fd) := by
  nested_suspension_source [filesLookupFdRaw] using [get_files,fdt_slot]

theorem fget_light (fd : Nat) (mask : UInt32) : Keeps (fgetLight fd mask) := by
  nested_suspension_source [fgetLight] using [get_files,compare,lookup_fd,branch,get_file,invariant,unsupported]

theorem fd_get (fd : Nat) : Keeps (fdget fd) := by
  nested_suspension_source [fdget] using [fget_light]

theorem fd_put (f : Fd) : Keeps (fdput f) := by
  nested_suspension_source [fdput] using [branch,fput_reference]

theorem set_fd_slot (fd : Nat) (value : Option FileId) : Keeps (setFdtSlot fd value) := by
  nested_suspension_source [setFdtSlot,_private.Leanux.FS.Stores.«0».Leanux.setAt] using [get_files,invariant,modify_fdt]

theorem set_fd_open (fd : Nat) (value : Bool) : Keeps (setFdtOpen fd value) := by
  nested_suspension_source [setFdtOpen,_private.Leanux.FS.Stores.«0».Leanux.setAt] using [get_files,invariant,modify_fdt]

theorem set_fd_cloexec (fd : Nat) (value : Bool) : Keeps (setFdtCloexec fd value) := by
  nested_suspension_source [setFdtCloexec,_private.Leanux.FS.Stores.«0».Leanux.setAt] using [get_files,invariant,modify_fdt]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
