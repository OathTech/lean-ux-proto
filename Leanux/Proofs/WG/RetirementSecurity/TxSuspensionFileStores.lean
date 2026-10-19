import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionNested

/-! Exact file and task-store leaves preserve suspended workers. File layer
state writes are allowed; ambient consumers remain individually justified. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

theorem task_read (ref : TaskRef) : TxSuspension.Keeps (TaskM.getTask ref) := by
  suspension_source [TaskM.getTask] using [TxSuspension.invariant]

theorem task_write (ref : TaskRef) (f : Task→Task) : TxSuspension.Keeps (TaskM.modifyTask ref f) := by
  suspension_source [TaskM.modifyTask] using [TxSuspension.invariant]

theorem get_task (ref : TaskRef) : Keeps (getTask ref : FS.M Task) := lift (task_read ref)
theorem modify_task (ref : TaskRef) (f : Task→Task) : Keeps (modifyTask ref f : FS.M Unit) := lift (task_write ref f)

theorem get_files : Keeps (getFiles : FS.M FilesStruct) := by
  nested_suspension_source [getFiles] using [get_task]

theorem modify_files (f : FilesStruct→FilesStruct) : Keeps (modifyFiles f : FS.M Unit) := by
  nested_suspension_source [modifyFiles] using [modify_task]

theorem modify_fdt (f : Fdtable→Fdtable) : Keeps (modifyFdt f : FS.M Unit) := by
  nested_suspension_source [modifyFdt] using [modify_files]

theorem get_file (slot : FileId) : Keeps (getFile slot) := by
  nested_suspension_source [getFile] using [invariant]

theorem set_file (slot : FileId) (value : File) : Keeps (setFile slot value) := modify _

theorem free_file (slot : FileId) : Keeps (freeFile slot) := modify _

theorem get_ctx (slot : CtxId) : Keeps (getCtx slot) := by
  nested_suspension_source [getCtx] using [invariant]

theorem set_ctx (slot : CtxId) (value : EventfdCtx) : Keeps (setCtx slot value) := modify _

theorem free_ctx (slot : CtxId) : Keeps (freeCtx slot) := modify _

theorem get_inode (slot : PipefsInodeId) : Keeps (getInode slot) := by
  nested_suspension_source [getInode] using [invariant]

theorem set_inode (slot : PipefsInodeId) (value : Inode) : Keeps (setInode slot value) := modify _

theorem get_pipe (slot : PipeId) : Keeps (getPipe slot) := by
  nested_suspension_source [getPipe] using [invariant]

theorem set_pipe (slot : PipeId) (value : PipeInodeInfo) : Keeps (setPipe slot value) := modify _

theorem get_page (slot : PageId) : Keeps (getPage slot) := by
  nested_suspension_source [getPage] using [invariant]

theorem set_page (slot : PageId) (value : Page) : Keeps (setPage slot value) := modify _

theorem get_ep (slot : EpId) : Keeps (getEp slot) := by
  nested_suspension_source [getEp] using [invariant]

theorem set_ep (slot : EpId) (value : Eventpoll) : Keeps (setEp slot value) := modify _

theorem free_ep (slot : EpId) : Keeps (freeEp slot) := modify _

theorem get_epi (slot : EpiId) : Keeps (getEpi slot) := by
  nested_suspension_source [getEpi] using [invariant]

theorem set_epi (slot : EpiId) (value : Epitem) : Keeps (setEpi slot value) := modify _

theorem free_epi (slot : EpiId) : Keeps (freeEpi slot) := modify _

theorem get_pwq (slot : PwqId) : Keeps (getPwq slot) := by
  nested_suspension_source [getPwq] using [invariant]

theorem set_pwq (slot : PwqId) (value : EppollEntry) : Keeps (setPwq slot value) := modify _

theorem free_pwq (slot : PwqId) : Keeps (freePwq slot) := modify _

theorem fdt_slot (fdt : Fdtable) (n : Nat) : Keeps (fdtSlot fdt n) := by
  nested_suspension_source [fdtSlot,_private.Leanux.FS.Stores.«0».Leanux.at?] using [invariant]

theorem fdt_open (fdt : Fdtable) (n : Nat) : Keeps (fdtOpen fdt n) := by
  nested_suspension_source [fdtOpen,_private.Leanux.FS.Stores.«0».Leanux.at?] using [invariant]

theorem fdt_cloexec (fdt : Fdtable) (n : Nat) : Keeps (fdtCloexec fdt n) := by
  nested_suspension_source [fdtCloexec,_private.Leanux.FS.Stores.«0».Leanux.at?] using [invariant]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
