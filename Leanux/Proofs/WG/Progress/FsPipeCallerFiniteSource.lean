import Leanux.Proofs.WG.Progress.PipeReadSource
import Leanux.Proofs.WG.Progress.PipeWriteOuterSource
import Leanux.Proofs.WG.Progress.PipeFreeSource
import Leanux.FS.Fput

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-- Actual read-iterator dispatch with the finite pipe evaluator. Other arms
are finite eventfd code or the original explicit refusal. -/
def fopReadIter (iocb : Kiocb) (count : Nat) : Option FopsId → FS.M Int
  | some .eventfd => eventfdRead iocb count
  | some .pipefifo => PipeRead.finite iocb count
  | some .eventpoll => invariant "eventpoll_fops has no read_iter (FMODE_CAN_READ is never set)"
  | some (.fixture name) => unsupported s!"read_iter of fixture file {name}"
  | none => invariant "file->f_op is NULL"

theorem fopReadIter_source (iocb : Kiocb) (count : Nat) (ops : Option FopsId) :
    Leanux.fopReadIter iocb count ops = fopReadIter iocb count ops := by
  cases ops with
  | none => rfl
  | some op =>
    cases op <;> simp only [Leanux.fopReadIter, fopReadIter, PipeRead.finite_source]

/-- Actual write-iterator dispatch with the finite whole pipe write. -/
def fopWriteIter (iocb : Kiocb) («from» : IovIter) : Option FopsId → FS.M Int
  | some .pipefifo => PipeWriteOuter.finite iocb «from»
  | some .eventfd => invariant "eventfd_fops has no write_iter (fopsOf routes it to write)"
  | some .eventpoll => invariant "eventpoll_fops has no write_iter (FMODE_CAN_WRITE is never set)"
  | some (.fixture name) => unsupported s!"write_iter of fixture file {name}"
  | none => invariant "file->f_op is NULL"

theorem fopWriteIter_source (iocb : Kiocb) (src : IovIter) (ops : Option FopsId) :
    Leanux.fopWriteIter iocb src ops = fopWriteIter iocb src ops := by
  cases ops with
  | none => rfl
  | some op =>
    cases op <;> simp only [Leanux.fopWriteIter, fopWriteIter, PipeWriteOuter.finite_source]

/-- Original final pipe-reference test and inode unlink, with finite freeing. -/
def putPipeInfo (ino : PipefsInodeId) (pid : PipeId) : FS.M Unit := do
  let p ← getPipe pid
  if p.files == 0 then invariant "put_pipe_info with pipe->files == 0"
  let files := p.files - 1
  setPipe pid { p with files }
  let kill ← do
    if ← branchCmp .putPipeInfoLast (files == 0) files 0 then
      setInode ino { (← getInode ino) with iPipe := none }
      pure true
    else pure false
  if ← branch .putPipeInfoKill kill then PipeFree.finite pid

theorem putPipeInfo_source (ino : PipefsInodeId) (pid : PipeId) :
    Leanux.putPipeInfo ino pid = putPipeInfo ino pid := by
  unfold Leanux.putPipeInfo putPipeInfo
  rw [PipeFree.finite_source]

/-- Release retains the original reader/writer accounting, actual wakeups and
final reference payment. Wake callbacks use their existing explicit fuel. -/
def pipeRelease (ino : PipefsInodeId) (fid : FileId) : FS.M Int := do
  let f ← getFile fid
  let pid ← pipeOf f
  -- mutex_lock(&pipe->mutex)
  if ← branchCmp .pipeReleaseRead (hasFlag f.fMode FMODE_READ) (f.fMode &&& FMODE_READ).toNat 0 then
    let p ← getPipe pid
    if p.readers == 0 then invariant "pipe_release: readers below zero"
    setPipe pid { p with readers := p.readers - 1 }
  if ← branchCmp .pipeReleaseWrite (hasFlag f.fMode FMODE_WRITE) (f.fMode &&& FMODE_WRITE).toNat 0 then
    let p ← getPipe pid
    if p.writers == 0 then invariant "pipe_release: writers below zero"
    setPipe pid { p with writers := p.writers - 1 }
  let p ← getPipe pid
  -- `!pipe->readers != !pipe->writers`
  if ← branch .pipeReleaseOneSide ((p.readers == 0) != (p.writers == 0)) then
    wakeUpInterruptibleAll (.pipeRd pid)
    wakeUpInterruptibleAll (.pipeWr pid)
    killFasync p.fasyncReaders
    killFasync p.fasyncWriters
  -- mutex_unlock(&pipe->mutex)
  putPipeInfo ino pid
  return 0

theorem pipeRelease_source (ino : PipefsInodeId) (fid : FileId) :
    Leanux.pipeRelease ino fid = pipeRelease ino fid := by
  unfold Leanux.pipeRelease pipeRelease
  have same : Leanux.putPipeInfo = putPipeInfo := funext fun node => funext (putPipeInfo_source node)
  rw [same]

/-- Actual release dispatch. Epoll teardown is already finite list/range code;
its ordinary fput only enqueues later task work. -/
def fopRelease (fid : FileId) : Option FopsId → FS.M Int
  | some .eventfd => eventfdRelease fid
  | some .pipefifo => do
    -- pipe_release(inode, file): `inode` is the file's pipefs inode
    match (← getFile fid).fInode with
    | some (.pipefs ino) => pipeRelease ino fid
    | _ => invariant "a pipefifo file whose f_inode is not a pipefs inode"
  | some .eventpoll => epEventpollRelease fid
  -- W8: sock_close (net/socket.c, unanchored): the socket's release and its
  -- RCU-deferred put_net are a cut point
  | some (.fixture _) => return 0
  | none => invariant "file->f_op is NULL"

theorem fopRelease_source (fid : FileId) (ops : Option FopsId) :
    Leanux.fopRelease fid ops = fopRelease fid ops := by
  cases ops with
  | none => rfl
  | some op =>
    cases op <;> simp only [Leanux.fopRelease, fopRelease]
    have same : Leanux.pipeRelease = pipeRelease := funext fun ino => funext (pipeRelease_source ino)
    rw [same]
    rfl

end Leanux.Proofs.WG.Progress.FsFinite
