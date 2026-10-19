import Leanux.Proofs.WG.Progress.FsAnonymousFiniteSource
import Leanux.Proofs.WG.Progress.FsPipeCallerFiniteSource
import Leanux.FS.PipeCreate

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Concrete finite pipe inode/file creation. Allocation and cleanup order,
including deferred ordinary fput, follows the original source. -/

def getPipeInode : FS.M (Option PipefsInodeId) := do
  let ino? ← newInodePseudo  -- new_inode_pseudo(pipe_mnt->mnt_sb)
  if ← branch .getPipeInodeNoInode ino?.isNone then return none  -- fail_inode
  let some ino := ino? | invariant "unreachable"
  let pipe? ← allocPipeInfo
  if ← branch .getPipeInodeNoPipe pipe?.isNone then
    iputPipefs ino  -- fail_iput
    return none
  let some pid := pipe? | invariant "unreachable"
  setInode ino { (← getInode ino) with iPipe := some pid }
  setPipe pid { (← getPipe pid) with files := 2, readers := 1, writers := 1 }
  -- inode->i_fop = &pipefifo_fops
  setInode ino { (← getInode ino) with iState := I_DIRTY, iMode := S_IFIFO ||| S_IRUSR ||| S_IWUSR }
  -- inode->i_uid = current_fsuid(); inode->i_gid = current_fsgid()
  _ ← simpleInodeInitTs ino
  return some ino

theorem getPipeInode_source :
    Leanux.getPipeInode = getPipeInode := by
  unfold Leanux.getPipeInode getPipeInode
  simp only [allocPipeInfo_source]
  rfl

def allocFileClone (base : FileId) (flags : UInt32) (fopId : FopsId) : FS.M (Except Int FileId) := do
  let some inode := (← getFile base).fInode | invariant "alloc_file_clone of a file with a NULL f_inode"
  let f ← allocFile flags fopId inode
  if ← branch .allocFileCloneOk (f matches .ok _) then
    match inode with
    | .pipefs ino => setInode ino { (← getInode ino) with dCount := (← getInode ino).dCount + 1 }
    | _ => unsupported "alloc_file_clone of a file outside pipefs"
  return f

theorem allocFileClone_source (base : FileId) (flags : UInt32) (fopId : FopsId) :
    Leanux.allocFileClone base flags fopId = allocFileClone base flags fopId := by
  unfold Leanux.allocFileClone allocFileClone
  simp only [allocFile_source]
  rfl

def createPipeFiles (flags : UInt32) : FS.M (Except Int (FileId × FileId)) := do
  let ino? ← getPipeInode
  if ← branch .createPipeFilesNoInode ino?.isNone then return .error (-ENFILE)
  let some ino := ino? | invariant "unreachable"
  let iPipe : FS.M PipeId := do
    match (← getInode ino).iPipe with
    | some pid => pure pid
    | none => invariant "create_pipe_files: inode->i_pipe is NULL"
  if ← branchCmp .createPipeFilesNotification (hasFlag flags O_NOTIFICATION_PIPE)
      (flags &&& O_NOTIFICATION_PIPE).toNat 0 then
    -- error = watch_queue_init(inode->i_pipe): the -ENOPKG stub
    -- (include/linux/watch_queue.h:126-128); `if (error)` folds away
    PipeFree.finite (← iPipe)
    iputPipefs ino
    return .error (-ENOPKG)
  let f ← allocFilePseudo (O_WRONLY ||| (flags &&& (O_NONBLOCK ||| O_DIRECT))) (.pipefs ino) .pipefifo
  if ← branch .createPipeFilesWriterErr (f matches .error _) then
    PipeFree.finite (← iPipe)
    iputPipefs ino
    return match f with | .error e => .error e | .ok _ => .error 0
  let .ok fw := f | invariant "unreachable"
  let pid ← iPipe
  setFile fw { (← getFile fw) with privateData := some (.pipe pid), fPipe := 0 }
  let r ← allocFileClone fw (O_RDONLY ||| (flags &&& O_NONBLOCK)) .pipefifo
  if ← branch .createPipeFilesReaderErr (r matches .error _) then
    putPipeInfo ino pid
    fput fw
    return match r with | .error e => .error e | .ok _ => .error 0
  let .ok fr := r | invariant "unreachable"
  setFile fr { (← getFile fr) with privateData := some (.pipe pid), fPipe := 0 }
  streamOpen fr
  streamOpen fw
  return .ok (fr, fw)

theorem createPipeFiles_source (flags : UInt32) :
    Leanux.createPipeFiles flags = createPipeFiles flags := by
  unfold Leanux.createPipeFiles createPipeFiles
  simp only [getPipeInode_source, PipeFree.finite_source, allocFilePseudo_source, allocFileClone_source, putPipeInfo_source]
  rfl


end Leanux.Proofs.WG.Progress.FsFinite
