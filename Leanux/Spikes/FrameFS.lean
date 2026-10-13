import Leanux.Syscalls
import Leanux.Spikes.FrameFSBase
import Leanux.Spikes.FrameWGBase

/-! Receive-snapshot framing through descriptor, file and pipe syscall callers,
and the original deferred file-release loop. -/

namespace Leanux.Spikes.Lifetimes.FSFrames
open Leanux Leanux.WG Std.Do Leanux.Spikes.Lifetimes Leanux.Spikes.Framing
open Leanux.Spikes.Lifetimes.KernelFrames Leanux.Spikes.Lifetimes.WGFrames
open Leanux.Spikes.Lifetimes.PipeFrames Leanux.Spikes.Lifetimes.PipeAux

set_option maxHeartbeats 800000
set_option pp.structureInstances false

theorem allocFile_sameSnapshot (flags : UInt32) (fopId : FopsId) (inode : InodeId) : SameSnapshot (Leanux.allocFile flags fopId inode) := by
  frame_same [Leanux.allocFile] using [allocEmptyFile_spec, fileInitPath_spec]

theorem allocFile_spec (P : Snapshot → Prop) (flags : UInt32) (fopId : FopsId) (inode : InodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.allocFile flags fopId inode
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allocFile_sameSnapshot flags fopId inode).wp P

theorem eventfdRelease_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.eventfdRelease fid) := by
  frame_same [Leanux.eventfdRelease] using [eventfdCtxOf_spec, eventfdCtxPut_spec, getCtx_spec, getFile_spec]

theorem eventfdRelease_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventfdRelease fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventfdRelease_sameSnapshot fid).wp P

theorem expandFiles_sameSnapshot (nr : Nat) : SameSnapshot (Leanux.expandFiles nr) := by
  frame_same [Leanux.expandFiles] using [expandFdtable_spec]

theorem expandFiles_spec (P : Snapshot → Prop) (nr : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.expandFiles nr
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (expandFiles_sameSnapshot nr).wp P

theorem fdget_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.fdget fd) := by
  frame_same [Leanux.fdget] using [fgetLight_spec]

theorem fdget_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fdget fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fdget_sameSnapshot fd).wp P

theorem fdgetRaw_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.fdgetRaw fd) := by
  frame_same [Leanux.fdgetRaw] using [fgetLight_spec]

theorem fdgetRaw_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fdgetRaw fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fdgetRaw_sameSnapshot fd).wp P

theorem fdput_sameSnapshot (f : Fd) : SameSnapshot (Leanux.fdput f) := by
  frame_same [Leanux.fdput] using [fput_spec]

theorem fdput_spec (P : Snapshot → Prop) (f : Fd) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fdput f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fdput_sameSnapshot f).wp P

theorem fgetFilesRcu_sameSnapshot (fd : Nat) (mask : UInt32) : SameSnapshot (Leanux.fgetFilesRcu fd mask) := by
  frame_same [Leanux.fgetFilesRcu] using [filesLookupFdRaw_spec, fput_spec, getFile_spec, setFile_spec]

theorem fgetFilesRcu_spec (P : Snapshot → Prop) (fd : Nat) (mask : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fgetFilesRcu fd mask
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fgetFilesRcu_sameSnapshot fd mask).wp P

theorem fileCloseFdLocked_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.fileCloseFdLocked fd) := by
  frame_same [Leanux.fileCloseFdLocked] using [fdtSlot_spec, putUnusedFdLocked_spec, setFdtSlot_spec]

theorem fileCloseFdLocked_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fileCloseFdLocked fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileCloseFdLocked_sameSnapshot fd).wp P

theorem filpClose_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.filpClose fid) := by
  frame_same [Leanux.filpClose] using [filpFlush_spec, fput_spec]

theorem filpClose_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.filpClose fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (filpClose_sameSnapshot fid).wp P

theorem fopReadIter_sameSnapshot (iocb : Kiocb) (count : Nat) (which : Option FopsId) : SameSnapshot (Leanux.fopReadIter iocb count which) := by
  cases which with
  | none => frame_same [Leanux.fopReadIter] using [eventfdRead_spec, pipeRead_spec]
  | some k => cases k <;> frame_same [Leanux.fopReadIter] using [eventfdRead_spec, pipeRead_spec]

theorem fopReadIter_spec (P : Snapshot → Prop) (iocb : Kiocb) (count : Nat) (which : Option FopsId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fopReadIter iocb count which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fopReadIter_sameSnapshot iocb count which).wp P

theorem fopWrite_sameSnapshot (fid : FileId) (buf : ByteArray) (count : Nat) (which : Option FopsId) : SameSnapshot (Leanux.fopWrite fid buf count which) := by
  cases which with
  | none => frame_same [Leanux.fopWrite] using [eventfdWrite_spec]
  | some k => cases k <;> frame_same [Leanux.fopWrite] using [eventfdWrite_spec]

theorem fopWrite_spec (P : Snapshot → Prop) (fid : FileId) (buf : ByteArray) (count : Nat) (which : Option FopsId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fopWrite fid buf count which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fopWrite_sameSnapshot fid buf count which).wp P

theorem getPipeInode_sameSnapshot  : SameSnapshot (Leanux.getPipeInode ) := by
  frame_same [Leanux.getPipeInode] using [allocPipeInfo_spec, getInode_spec, getPipe_spec, iputPipefs_spec, newInodePseudo_spec, setInode_spec, setPipe_spec, simpleInodeInitTs_spec]

theorem getPipeInode_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getPipeInode
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getPipeInode_sameSnapshot ).wp P

theorem pipeSetSize_sameSnapshot (pid : PipeId) (arg : Nat) : SameSnapshot (Leanux.pipeSetSize pid arg) := by
  frame_same [Leanux.pipeSetSize] using [accountPipeBuffers_spec, getPipe_spec, pipeIsUnprivilegedUser_spec, pipeResizeRing_spec, roundPipeSize_spec, tooManyPipeBuffersHard_spec, tooManyPipeBuffersSoft_spec]

theorem pipeSetSize_spec (P : Snapshot → Prop) (pid : PipeId) (arg : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipeSetSize pid arg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeSetSize_sameSnapshot pid arg).wp P

theorem putUnusedFd_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.putUnusedFd fd) := by
  frame_same [Leanux.putUnusedFd] using [putUnusedFdLocked_spec]

theorem putUnusedFd_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.putUnusedFd fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (putUnusedFd_sameSnapshot fd).wp P

theorem allocFd_sameSnapshot (start «end» : Nat) (flags : UInt32) : SameSnapshot (Leanux.allocFd start «end» flags) := by
  frame_same [Leanux.allocFd] using [clearCloseOnExecBit_spec, expandFiles_spec, fdtSlot_spec, findNextFd_spec, setCloseOnExecBit_spec, setOpenFd_spec]

theorem allocFd_spec (P : Snapshot → Prop) (start «end» : Nat) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.allocFd start «end» flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allocFd_sameSnapshot start «end» flags).wp P

theorem allocFileClone_sameSnapshot (base : FileId) (flags : UInt32) (fopId : FopsId) : SameSnapshot (Leanux.allocFileClone base flags fopId) := by
  frame_same [Leanux.allocFileClone] using [allocFile_spec, getFile_spec, getInode_spec, setInode_spec]

theorem allocFileClone_spec (P : Snapshot → Prop) (base : FileId) (flags : UInt32) (fopId : FopsId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.allocFileClone base flags fopId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allocFileClone_sameSnapshot base flags fopId).wp P

theorem allocFilePseudo_sameSnapshot (flags : UInt32) (inode : InodeId) (fopId : FopsId) : SameSnapshot (Leanux.allocFilePseudo flags inode fopId) := by
  frame_same [Leanux.allocFilePseudo] using [allocFile_spec, allocPathPseudo_spec, getInode_spec, setInode_spec]

theorem allocFilePseudo_spec (P : Snapshot → Prop) (flags : UInt32) (inode : InodeId) (fopId : FopsId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.allocFilePseudo flags inode fopId
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allocFilePseudo_sameSnapshot flags inode fopId).wp P

theorem doDup2_sameSnapshot (fid : FileId) (fd : Nat) (flags : UInt32) : SameSnapshot (Leanux.doDup2 fid fd flags) := by
  frame_same [Leanux.doDup2] using [clearCloseOnExecBit_spec, fdtOpen_spec, fdtSlot_spec, filpClose_spec, getFileRef_spec, setCloseOnExecBit_spec, setFdtSlot_spec, setOpenFd_spec]

theorem doDup2_spec (P : Snapshot → Prop) (fid : FileId) (fd : Nat) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doDup2 fid fd flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doDup2_sameSnapshot fid fd flags).wp P

theorem fdgetPos_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.fdgetPos fd) := by
  frame_same [Leanux.fdgetPos] using [fdget_spec, fopsOf_spec, getFile_spec]

theorem fdgetPos_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fdgetPos fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fdgetPos_sameSnapshot fd).wp P

theorem fdputPos_sameSnapshot (f : Fd) : SameSnapshot (Leanux.fdputPos f) := by
  frame_same [Leanux.fdputPos] using [fdput_spec]

theorem fdputPos_spec (P : Snapshot → Prop) (f : Fd) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fdputPos f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fdputPos_sameSnapshot f).wp P

theorem fgetRaw_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.fgetRaw fd) := by
  frame_same [Leanux.fgetRaw] using [fgetFilesRcu_spec]

theorem fgetRaw_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fgetRaw fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fgetRaw_sameSnapshot fd).wp P

theorem fileCloseFd_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.fileCloseFd fd) := by
  frame_same [Leanux.fileCloseFd] using [fileCloseFdLocked_spec]

theorem fileCloseFd_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fileCloseFd fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileCloseFd_sameSnapshot fd).wp P

theorem fopRelease_sameSnapshot (fid : FileId) (which : Option FopsId) : SameSnapshot (Leanux.fopRelease fid which) := by
  cases which with
  | none => frame_same [Leanux.fopRelease] using [eventfdRelease_spec, getFile_spec, pipeRelease_spec]
  | some k => cases k <;> frame_same [Leanux.fopRelease] using [eventfdRelease_spec, getFile_spec, pipeRelease_spec]

theorem fopRelease_spec (P : Snapshot → Prop) (fid : FileId) (which : Option FopsId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fopRelease fid which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fopRelease_sameSnapshot fid which).wp P

theorem newSyncRead_sameSnapshot (fid : FileId) (len : Nat) (ppos : Option Int) : SameSnapshot (Leanux.newSyncRead fid len ppos) := by
  frame_same [Leanux.newSyncRead] using [fopReadIter_spec, getFile_spec]

theorem newSyncRead_spec (P : Snapshot → Prop) (fid : FileId) (len : Nat) (ppos : Option Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.newSyncRead fid len ppos
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (newSyncRead_sameSnapshot fid len ppos).wp P

theorem pipeFcntl_sameSnapshot (fid : FileId) (cmd : Nat) (arg : Nat) : SameSnapshot (Leanux.pipeFcntl fid cmd arg) := by
  frame_same [Leanux.pipeFcntl] using [getFile_spec, getPipeInfo_spec, getPipe_spec, pipeSetSize_spec]

theorem pipeFcntl_spec (P : Snapshot → Prop) (fid : FileId) (cmd : Nat) (arg : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipeFcntl fid cmd arg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeFcntl_sameSnapshot fid cmd arg).wp P

theorem vfsWrite_sameSnapshot (fid : FileId) (buf : ByteArray) (count : Nat) (pos : Option Int) : SameSnapshot (Leanux.vfsWrite fid buf count pos) := by
  frame_same [Leanux.vfsWrite] using [fileEndWrite_spec, fileStartWrite_spec, fopWrite_spec, fopsOf_spec, getFile_spec, newSyncWrite_spec, rwVerifyArea_spec]

theorem vfsWrite_spec (P : Snapshot → Prop) (fid : FileId) (buf : ByteArray) (count : Nat) (pos : Option Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.vfsWrite fid buf count pos
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (vfsWrite_sameSnapshot fid buf count pos).wp P

theorem anonInodeGetfileImpl_sameSnapshot (fopId : FopsId) (priv : PrivateData) (flags : UInt32) (makeInode : Bool) : SameSnapshot (Leanux.anonInodeGetfileImpl fopId priv flags makeInode) := by
  frame_same [Leanux.anonInodeGetfileImpl] using [allocFilePseudo_spec, fopsOf_spec, getFile_spec, setFile_spec]

theorem anonInodeGetfileImpl_spec (P : Snapshot → Prop) (fopId : FopsId) (priv : PrivateData) (flags : UInt32) (makeInode : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.anonInodeGetfileImpl fopId priv flags makeInode
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (anonInodeGetfileImpl_sameSnapshot fopId priv flags makeInode).wp P

theorem createPipeFiles_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.createPipeFiles flags) := by
  frame_same [Leanux.createPipeFiles] using [allocFileClone_spec, allocFilePseudo_spec, fput_spec, freePipeInfo_spec, getFile_spec, getInode_spec, getPipeInode_spec, iputPipefs_spec, putPipeInfo_spec, setFile_spec, streamOpen_spec]

theorem createPipeFiles_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.createPipeFiles flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (createPipeFiles_sameSnapshot flags).wp P

theorem doFcntl_sameSnapshot (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) (fid : FileId) : SameSnapshot (Leanux.doFcntl fd cmd arg fid) := by
  frame_same [Leanux.doFcntl] using [getCloseOnExec_spec, getFile_spec, pipeFcntl_spec, setCloseOnExec_spec, setfl_spec]

theorem doFcntl_spec (P : Snapshot → Prop) (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doFcntl fd cmd arg fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doFcntl_sameSnapshot fd cmd arg fid).wp P

theorem fputFinal_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.fputFinal fid) := by
  frame_same [Leanux.fputFinal] using [dputPipefs_spec, fileFree_spec, fopRelease_spec, fopsOf_spec, getFile_spec, inodeIsChr_spec, putFileAccess_spec, queueDeviceWork_spec]

theorem fputFinal_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fputFinal fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fputFinal_sameSnapshot fid).wp P

theorem getUnusedFdFlags_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.getUnusedFdFlags flags) := by
  frame_same [Leanux.getUnusedFdFlags] using [allocFd_spec]

theorem getUnusedFdFlags_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getUnusedFdFlags flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getUnusedFdFlags_sameSnapshot flags).wp P

theorem ksysDup3_sameSnapshot (oldfd newfd : Nat) (flags : UInt32) : SameSnapshot (Leanux.ksysDup3 oldfd newfd flags) := by
  frame_same [Leanux.ksysDup3] using [doDup2_spec, expandFiles_spec, filesLookupFdRaw_spec]

theorem ksysDup3_spec (P : Snapshot → Prop) (oldfd newfd : Nat) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.ksysDup3 oldfd newfd flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ksysDup3_sameSnapshot oldfd newfd flags).wp P

theorem ksysWrite_sameSnapshot (fd : Nat) (buf : ByteArray) (count : Nat) : SameSnapshot (Leanux.ksysWrite fd buf count) := by
  frame_same [Leanux.ksysWrite] using [fdgetPos_spec, fdputPos_spec, filePpos_spec, getFile_spec, setFile_spec, vfsWrite_spec]

theorem ksysWrite_spec (P : Snapshot → Prop) (fd : Nat) (buf : ByteArray) (count : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.ksysWrite fd buf count
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ksysWrite_sameSnapshot fd buf count).wp P

theorem vfsRead_sameSnapshot (fid : FileId) (count : Nat) (pos : Option Int) : SameSnapshot (Leanux.vfsRead fid count pos) := by
  frame_same [Leanux.vfsRead] using [fopsOf_spec, getFile_spec, newSyncRead_spec, rwVerifyArea_spec]

theorem vfsRead_spec (P : Snapshot → Prop) (fid : FileId) (count : Nat) (pos : Option Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.vfsRead fid count pos
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (vfsRead_sameSnapshot fid count pos).wp P

theorem anonInodeGetfile_sameSnapshot (fopId : FopsId) (priv : PrivateData) (flags : UInt32) : SameSnapshot (Leanux.anonInodeGetfile fopId priv flags) := by
  frame_same [Leanux.anonInodeGetfile] using [anonInodeGetfileImpl_spec]

theorem anonInodeGetfile_spec (P : Snapshot → Prop) (fopId : FopsId) (priv : PrivateData) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.anonInodeGetfile fopId priv flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (anonInodeGetfile_sameSnapshot fopId priv flags).wp P

theorem doPipeFlags_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.doPipeFlags flags) := by
  frame_same [Leanux.doPipeFlags] using [createPipeFiles_spec, fput_spec, getFile_spec, getUnusedFdFlags_spec, putUnusedFd_spec, setFile_spec]

theorem doPipeFlags_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doPipeFlags flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doPipeFlags_sameSnapshot flags).wp P

theorem fputSync_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.fputSync fid) := by
  frame_same [Leanux.fputSync] using [fputFinal_spec, getFile_spec, setFile_spec]

theorem fputSync_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fputSync fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fputSync_sameSnapshot fid).wp P

theorem ksysRead_sameSnapshot (fd : Nat) (count : Nat) : SameSnapshot (Leanux.ksysRead fd count) := by
  frame_same [Leanux.ksysRead] using [fdgetPos_spec, fdputPos_spec, filePpos_spec, getFile_spec, setFile_spec, vfsRead_spec]

theorem ksysRead_spec (P : Snapshot → Prop) (fd : Nat) (count : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.ksysRead fd count
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ksysRead_sameSnapshot fd count).wp P

theorem sysDup_sameSnapshot (fildes : Nat) : SameSnapshot (Leanux.sysDup fildes) := by
  frame_same [Leanux.sysDup] using [fdInstall_spec, fgetRaw_spec, fput_spec, getUnusedFdFlags_spec]

theorem sysDup_spec (P : Snapshot → Prop) (fildes : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysDup fildes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysDup_sameSnapshot fildes).wp P

theorem sysFcntl_sameSnapshot (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) : SameSnapshot (Leanux.sysFcntl fd cmd arg) := by
  frame_same [Leanux.sysFcntl] using [doFcntl_spec, fdgetRaw_spec, fdput_spec, getFile_spec]

theorem sysFcntl_spec (P : Snapshot → Prop) (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysFcntl fd cmd arg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysFcntl_sameSnapshot fd cmd arg).wp P

theorem doEventfd_sameSnapshot (count : UInt32) (flags : UInt32) : SameSnapshot (Leanux.doEventfd count flags) := by
  frame_same [Leanux.doEventfd] using [anonInodeGetfile_spec, eventfdFreeCtx_spec, fdInstall_spec, getCtx_spec, getFile_spec, getUnusedFdFlags_spec, hiddenAlloc_snapshot_spec, idaAlloc_spec, putUnusedFd_spec, setCtx_spec, setFile_spec]

theorem doEventfd_spec (P : Snapshot → Prop) (count : UInt32) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doEventfd count flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doEventfd_sameSnapshot count flags).wp P

theorem doPipe2_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.doPipe2 flags) := by
  frame_same [Leanux.doPipe2] using [doPipeFlags_spec, fdInstall_spec, fput_spec, putUnusedFd_spec]

theorem doPipe2_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.doPipe2 flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doPipe2_sameSnapshot flags).wp P

theorem sysClose_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.sysClose fd) := by
  frame_same [Leanux.sysClose] using [fileCloseFd_spec, filpFlush_spec, fputSync_spec]

theorem sysClose_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysClose fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysClose_sameSnapshot fd).wp P

theorem sysEventfd2_sameSnapshot (count flags : UInt32) : SameSnapshot (Leanux.sysEventfd2 count flags) := by
  frame_same [Leanux.sysEventfd2] using [doEventfd_spec]

theorem sysEventfd2_spec (P : Snapshot → Prop) (count flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysEventfd2 count flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysEventfd2_sameSnapshot count flags).wp P

theorem sysPipe2_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.sysPipe2 flags) := by
  frame_same [Leanux.sysPipe2] using [doPipe2_spec]

theorem sysPipe2_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.sysPipe2 flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sysPipe2_sameSnapshot flags).wp P

theorem taskWorkRun_sameSnapshot : SameSnapshot Leanux.taskWorkRun := by
  frame_same [Leanux.taskWorkRun] using [fputFinal_spec]

theorem taskWorkRun_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.taskWorkRun
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := taskWorkRun_sameSnapshot.wp P

end Leanux.Spikes.Lifetimes.FSFrames
