import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionPipeLoop
import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionReleaseLeaves
import Leanux.Proofs.WG.RetirementSecurity.TxWorkDescriptorCalls

/-! Returning to user mode executes actual file-release callbacks. These
source contracts retain suspended worker records through the complete callback
family, including pipe loops, epoll recursion and cleanup-net work queueing. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

theorem pipe_put (ino : PipefsInodeId) (pid : PipeId) : Keeps (putPipeInfo ino pid) := by
  nested_suspension_source [putPipeInfo] using
    [get_pipe,set_pipe,get_inode,set_inode,invariant,branch,compare,pipe_free]

theorem fasync (present : Bool) : Keeps (killFasync present) := by
  nested_suspension_source [killFasync] using [branch,unsupported]

theorem pipe_release (ino : PipefsInodeId) (fid : FileId) : Keeps (pipeRelease ino fid) := by
  nested_suspension_source [pipeRelease] using
    [get_file,pipe_of,compare,branch,get_pipe,set_pipe,invariant,wake_interruptible_all,fasync,pipe_put]

theorem fop_release (fid : FileId) (ops : Option FopsId) : Keeps (fopRelease fid ops) := by
  nested_suspension_source [fopRelease] using [eventfd_release,get_file,pipe_release,ep_release,invariant]

theorem fput_final (fid : FileId) : Keeps (fputFinal fid) := by
  nested_suspension_source [fputFinal] using
    [get_file,compare,branch,file_free,ep_release_file,fops,unsupported,fop_release,
     inode_chr,file_access_put,pipe_dentry_put,iput,device_work]

theorem task_work : Keeps taskWorkRun := by
  nested_suspension_source [taskWorkRun] using [get_task,modify_task,fput_final,invariant]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested

namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.Proofs.Framing Lifetimes Queues

theorem task_work_actor :
    Preserves (At (Covered locals crypt) crypt active) (liftFS taskWorkRun) :=
  actor_files TxSuspension.Nested.task_work

end Leanux.Proofs.WG.RetirementSecurity.TxWork
