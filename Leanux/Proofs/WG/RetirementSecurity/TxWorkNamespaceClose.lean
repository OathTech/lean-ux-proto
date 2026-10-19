import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionTaskWork

/-! Namespace-holder close runs the original file releases before cleanup is
queued. The active/suspended service carrier survives these actual operations. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

theorem fd_unused (fd : Nat) : Keeps (putUnusedFdLocked fd) := by
  nested_suspension_source [putUnusedFdLocked,clearOpenFd] using
    [set_fd_open,compare,get_files,modify_files]

theorem fd_close_locked (fd : Nat) : Keeps (fileCloseFdLocked fd) := by
  nested_suspension_source [fileCloseFdLocked] using
    [get_files,compare,fdt_slot,branch,set_fd_slot,fd_unused]

theorem fd_close (fd : Nat) : Keeps (fileCloseFd fd) := by
  nested_suspension_source [fileCloseFd] using [fd_close_locked]

theorem filp_flush (fid : FileId) : Keeps (filpFlush fid) := by
  nested_suspension_source [filpFlush] using [get_file,compare,branch,fops,unsupported]

theorem fput_sync (fid : FileId) : Keeps (fputSync fid) := by
  nested_suspension_source [fputSync] using [get_file,set_file,branch,fput_final]

theorem sys_close (fd : Nat) : Keeps (sysClose fd) := by
  nested_suspension_source [sysClose] using [fd_close,branch,invariant,filp_flush,fput_sync]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested

namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.Proofs.Framing Lifetimes Queues

theorem namespace_close_actor :
    Preserves (At (Covered locals crypt) crypt active) netnsClose := by
  unfold netnsClose
  repeat' first
    | (tx_file_lift FS.M
       first
       | env_operation_fact TxSuspension.Nested.sys_close
       | env_operation_fact TxSuspension.Nested.task_work)
    | actor_control_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
