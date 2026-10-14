import Leanux.Syscalls
import Leanux.Proofs.Framing.FSBase
import Leanux.Proofs.Framing.Eventpoll

/-! Full WireGuard kernel framing through descriptor, file and pipe syscall callers,
and the original deferred file-release loop. -/

namespace Leanux.Proofs.Framing.FSFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.Framing.KernelFrames
open Leanux.Proofs.Framing.PipeFrames Leanux.Proofs.Framing.PipeAux Leanux.Proofs.Framing.WaitFrames
open Leanux.Proofs.Framing.EventpollFrames

set_option maxHeartbeats 800000
set_option pp.structureInstances false

theorem allocFile_sameWGKernel (flags : UInt32) (fopId : FopsId) (inode : InodeId) : SameWGKernel (Leanux.allocFile flags fopId inode) := by
  frame_wg [Leanux.allocFile] using [allocEmptyFile_spec, fileInitPath_spec]

theorem allocFile_spec (P : WGKernelView → Prop) (flags : UInt32) (fopId : FopsId) (inode : InodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.allocFile flags fopId inode
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (allocFile_sameWGKernel flags fopId inode).wp P

theorem eventfdRelease_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.eventfdRelease fid) := by
  frame_wg [Leanux.eventfdRelease] using [eventfdCtxOf_spec, eventfdCtxPut_spec, getCtx_spec, getFile_spec,
    wakeUpPoll_spec]

theorem eventfdRelease_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.eventfdRelease fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (eventfdRelease_sameWGKernel fid).wp P

theorem expandFiles_sameWGKernel (nr : Nat) : SameWGKernel (Leanux.expandFiles nr) := by
  frame_wg [Leanux.expandFiles] using [expandFdtable_spec]

theorem expandFiles_spec (P : WGKernelView → Prop) (nr : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.expandFiles nr
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (expandFiles_sameWGKernel nr).wp P

theorem fdget_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.fdget fd) := by
  frame_wg [Leanux.fdget] using [fgetLight_spec]

theorem fdget_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fdget fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fdget_sameWGKernel fd).wp P

theorem fdgetRaw_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.fdgetRaw fd) := by
  frame_wg [Leanux.fdgetRaw] using [fgetLight_spec]

theorem fdgetRaw_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fdgetRaw fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fdgetRaw_sameWGKernel fd).wp P

theorem fdput_sameWGKernel (f : Fd) : SameWGKernel (Leanux.fdput f) :=
  (Framing.FSFileRefs.fdput_sameWGKernel f)

theorem fdput_spec (P : WGKernelView → Prop) (f : Fd) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fdput f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fdput_sameWGKernel f).wp P

theorem fgetFilesRcu_sameWGKernel (fd : Nat) (mask : UInt32) : SameWGKernel (Leanux.fgetFilesRcu fd mask) := by
  frame_wg [Leanux.fgetFilesRcu] using [filesLookupFdRaw_spec, fput_spec, getFile_spec, setFile_spec]

theorem fgetFilesRcu_spec (P : WGKernelView → Prop) (fd : Nat) (mask : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fgetFilesRcu fd mask
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fgetFilesRcu_sameWGKernel fd mask).wp P

theorem fileCloseFdLocked_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.fileCloseFdLocked fd) := by
  frame_wg [Leanux.fileCloseFdLocked] using [fdtSlot_spec, putUnusedFdLocked_spec, setFdtSlot_spec]

theorem fileCloseFdLocked_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fileCloseFdLocked fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fileCloseFdLocked_sameWGKernel fd).wp P

theorem filpClose_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.filpClose fid) := by
  frame_wg [Leanux.filpClose] using [filpFlush_spec, fput_spec]

theorem filpClose_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.filpClose fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (filpClose_sameWGKernel fid).wp P

theorem fopReadIter_sameWGKernel (iocb : Kiocb) (count : Nat) (which : Option FopsId) : SameWGKernel (Leanux.fopReadIter iocb count which) := by
  cases which with
  | none => frame_wg [Leanux.fopReadIter] using [eventfdRead_spec, pipeRead_spec]
  | some k => cases k <;> frame_wg [Leanux.fopReadIter] using [eventfdRead_spec, pipeRead_spec]

theorem fopReadIter_spec (P : WGKernelView → Prop) (iocb : Kiocb) (count : Nat) (which : Option FopsId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fopReadIter iocb count which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fopReadIter_sameWGKernel iocb count which).wp P

theorem fopWrite_sameWGKernel (fid : FileId) (buf : ByteArray) (count : Nat) (which : Option FopsId) : SameWGKernel (Leanux.fopWrite fid buf count which) := by
  cases which with
  | none => frame_wg [Leanux.fopWrite] using [eventfdWrite_spec]
  | some k => cases k <;> frame_wg [Leanux.fopWrite] using [eventfdWrite_spec]

theorem fopWrite_spec (P : WGKernelView → Prop) (fid : FileId) (buf : ByteArray) (count : Nat) (which : Option FopsId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fopWrite fid buf count which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fopWrite_sameWGKernel fid buf count which).wp P

theorem getPipeInode_sameWGKernel  : SameWGKernel (Leanux.getPipeInode ) := by
  frame_wg [Leanux.getPipeInode] using [allocPipeInfo_spec, getInode_spec, getPipe_spec, iputPipefs_spec, newInodePseudo_spec, setInode_spec, setPipe_spec, simpleInodeInitTs_spec]

theorem getPipeInode_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getPipeInode
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getPipeInode_sameWGKernel ).wp P

theorem pipeSetSize_sameWGKernel (pid : PipeId) (arg : Nat) : SameWGKernel (Leanux.pipeSetSize pid arg) := by
  frame_wg [Leanux.pipeSetSize] using [accountPipeBuffers_spec, getPipe_spec, pipeIsUnprivilegedUser_spec, pipeResizeRing_spec, roundPipeSize_spec, tooManyPipeBuffersHard_spec, tooManyPipeBuffersSoft_spec]

theorem pipeSetSize_spec (P : WGKernelView → Prop) (pid : PipeId) (arg : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipeSetSize pid arg
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pipeSetSize_sameWGKernel pid arg).wp P

theorem putUnusedFd_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.putUnusedFd fd) := by
  frame_wg [Leanux.putUnusedFd] using [putUnusedFdLocked_spec]

theorem putUnusedFd_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.putUnusedFd fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (putUnusedFd_sameWGKernel fd).wp P

theorem allocFd_sameWGKernel (start «end» : Nat) (flags : UInt32) : SameWGKernel (Leanux.allocFd start «end» flags) := by
  frame_wg [Leanux.allocFd] using [clearCloseOnExecBit_spec, expandFiles_spec, fdtSlot_spec, findNextFd_spec, setCloseOnExecBit_spec, setOpenFd_spec]

theorem allocFd_spec (P : WGKernelView → Prop) (start «end» : Nat) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.allocFd start «end» flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (allocFd_sameWGKernel start «end» flags).wp P

theorem allocFileClone_sameWGKernel (base : FileId) (flags : UInt32) (fopId : FopsId) : SameWGKernel (Leanux.allocFileClone base flags fopId) := by
  frame_wg [Leanux.allocFileClone] using [allocFile_spec, getFile_spec, getInode_spec, setInode_spec]

theorem allocFileClone_spec (P : WGKernelView → Prop) (base : FileId) (flags : UInt32) (fopId : FopsId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.allocFileClone base flags fopId
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (allocFileClone_sameWGKernel base flags fopId).wp P

theorem allocFilePseudo_sameWGKernel (flags : UInt32) (inode : InodeId) (fopId : FopsId) : SameWGKernel (Leanux.allocFilePseudo flags inode fopId) := by
  frame_wg [Leanux.allocFilePseudo] using [allocFile_spec, allocPathPseudo_spec, getInode_spec, setInode_spec]

theorem allocFilePseudo_spec (P : WGKernelView → Prop) (flags : UInt32) (inode : InodeId) (fopId : FopsId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.allocFilePseudo flags inode fopId
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (allocFilePseudo_sameWGKernel flags inode fopId).wp P

theorem doDup2_sameWGKernel (fid : FileId) (fd : Nat) (flags : UInt32) : SameWGKernel (Leanux.doDup2 fid fd flags) := by
  frame_wg [Leanux.doDup2] using [clearCloseOnExecBit_spec, fdtOpen_spec, fdtSlot_spec, filpClose_spec, getFileRef_spec, setCloseOnExecBit_spec, setFdtSlot_spec, setOpenFd_spec]

theorem doDup2_spec (P : WGKernelView → Prop) (fid : FileId) (fd : Nat) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.doDup2 fid fd flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doDup2_sameWGKernel fid fd flags).wp P

theorem fdgetPos_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.fdgetPos fd) := by
  frame_wg [Leanux.fdgetPos] using [fdget_spec, fopsOf_spec, getFile_spec]

theorem fdgetPos_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fdgetPos fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fdgetPos_sameWGKernel fd).wp P

theorem fdputPos_sameWGKernel (f : Fd) : SameWGKernel (Leanux.fdputPos f) := by
  frame_wg [Leanux.fdputPos] using [fdput_spec]

theorem fdputPos_spec (P : WGKernelView → Prop) (f : Fd) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fdputPos f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fdputPos_sameWGKernel f).wp P

theorem fgetRaw_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.fgetRaw fd) := by
  frame_wg [Leanux.fgetRaw] using [fgetFilesRcu_spec]

theorem fgetRaw_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fgetRaw fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fgetRaw_sameWGKernel fd).wp P

theorem fileCloseFd_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.fileCloseFd fd) := by
  frame_wg [Leanux.fileCloseFd] using [fileCloseFdLocked_spec]

theorem fileCloseFd_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fileCloseFd fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fileCloseFd_sameWGKernel fd).wp P

theorem fopRelease_sameWGKernel (fid : FileId) (which : Option FopsId) : SameWGKernel (Leanux.fopRelease fid which) := by
  cases which with
  | none => frame_wg [Leanux.fopRelease] using [eventfdRelease_spec, getFile_spec, pipeRelease_spec]
  | some k => cases k <;> frame_wg [Leanux.fopRelease] using [eventfdRelease_spec, getFile_spec, pipeRelease_spec,
      epEventpollRelease_spec]

theorem fopRelease_spec (P : WGKernelView → Prop) (fid : FileId) (which : Option FopsId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fopRelease fid which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fopRelease_sameWGKernel fid which).wp P

theorem newSyncRead_sameWGKernel (fid : FileId) (len : Nat) (ppos : Option Int) : SameWGKernel (Leanux.newSyncRead fid len ppos) := by
  frame_wg [Leanux.newSyncRead] using [fopReadIter_spec, getFile_spec]

theorem newSyncRead_spec (P : WGKernelView → Prop) (fid : FileId) (len : Nat) (ppos : Option Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.newSyncRead fid len ppos
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (newSyncRead_sameWGKernel fid len ppos).wp P

theorem pipeFcntl_sameWGKernel (fid : FileId) (cmd : Nat) (arg : Nat) : SameWGKernel (Leanux.pipeFcntl fid cmd arg) := by
  frame_wg [Leanux.pipeFcntl] using [getFile_spec, getPipeInfo_spec, getPipe_spec, pipeSetSize_spec]

theorem pipeFcntl_spec (P : WGKernelView → Prop) (fid : FileId) (cmd : Nat) (arg : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipeFcntl fid cmd arg
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pipeFcntl_sameWGKernel fid cmd arg).wp P

theorem vfsWrite_sameWGKernel (fid : FileId) (buf : ByteArray) (count : Nat) (pos : Option Int) : SameWGKernel (Leanux.vfsWrite fid buf count pos) := by
  frame_wg [Leanux.vfsWrite] using [fileEndWrite_spec, fileStartWrite_spec, fopWrite_spec, fopsOf_spec, getFile_spec, newSyncWrite_spec, rwVerifyArea_spec]

theorem vfsWrite_spec (P : WGKernelView → Prop) (fid : FileId) (buf : ByteArray) (count : Nat) (pos : Option Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.vfsWrite fid buf count pos
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (vfsWrite_sameWGKernel fid buf count pos).wp P

theorem anonInodeGetfileImpl_sameWGKernel (fopId : FopsId) (priv : PrivateData) (flags : UInt32) (makeInode : Bool) : SameWGKernel (Leanux.anonInodeGetfileImpl fopId priv flags makeInode) := by
  frame_wg [Leanux.anonInodeGetfileImpl] using [allocFilePseudo_spec, fopsOf_spec, getFile_spec, setFile_spec]

theorem anonInodeGetfileImpl_spec (P : WGKernelView → Prop) (fopId : FopsId) (priv : PrivateData) (flags : UInt32) (makeInode : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.anonInodeGetfileImpl fopId priv flags makeInode
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (anonInodeGetfileImpl_sameWGKernel fopId priv flags makeInode).wp P

theorem createPipeFiles_sameWGKernel (flags : UInt32) : SameWGKernel (Leanux.createPipeFiles flags) := by
  frame_wg [Leanux.createPipeFiles] using [allocFileClone_spec, allocFilePseudo_spec, fput_spec, freePipeInfo_spec, getFile_spec, getInode_spec, getPipeInode_spec, iputPipefs_spec, putPipeInfo_spec, setFile_spec, streamOpen_spec]

theorem createPipeFiles_spec (P : WGKernelView → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.createPipeFiles flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (createPipeFiles_sameWGKernel flags).wp P

theorem doFcntl_sameWGKernel (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) (fid : FileId) : SameWGKernel (Leanux.doFcntl fd cmd arg fid) := by
  frame_wg [Leanux.doFcntl] using [getCloseOnExec_spec, getFile_spec, pipeFcntl_spec, setCloseOnExec_spec, setfl_spec]

theorem doFcntl_spec (P : WGKernelView → Prop) (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.doFcntl fd cmd arg fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doFcntl_sameWGKernel fd cmd arg fid).wp P

theorem fputFinal_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.fputFinal fid) := by
  frame_wg [Leanux.fputFinal] using [dputPipefs_spec, fileFree_spec, fopRelease_spec, fopsOf_spec, getFile_spec, inodeIsChr_spec, putFileAccess_spec, queueDeviceWork_spec,
    eventpollReleaseFile_spec]

theorem fputFinal_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fputFinal fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fputFinal_sameWGKernel fid).wp P

theorem getUnusedFdFlags_sameWGKernel (flags : UInt32) : SameWGKernel (Leanux.getUnusedFdFlags flags) := by
  frame_wg [Leanux.getUnusedFdFlags] using [allocFd_spec]

theorem getUnusedFdFlags_spec (P : WGKernelView → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getUnusedFdFlags flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getUnusedFdFlags_sameWGKernel flags).wp P

theorem ksysDup3_sameWGKernel (oldfd newfd : Nat) (flags : UInt32) : SameWGKernel (Leanux.ksysDup3 oldfd newfd flags) := by
  frame_wg [Leanux.ksysDup3] using [doDup2_spec, expandFiles_spec, filesLookupFdRaw_spec]

theorem ksysDup3_spec (P : WGKernelView → Prop) (oldfd newfd : Nat) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.ksysDup3 oldfd newfd flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (ksysDup3_sameWGKernel oldfd newfd flags).wp P

theorem ksysWrite_sameWGKernel (fd : Nat) (buf : ByteArray) (count : Nat) : SameWGKernel (Leanux.ksysWrite fd buf count) := by
  frame_wg [Leanux.ksysWrite] using [fdgetPos_spec, fdputPos_spec, filePpos_spec, getFile_spec, setFile_spec, vfsWrite_spec]

theorem ksysWrite_spec (P : WGKernelView → Prop) (fd : Nat) (buf : ByteArray) (count : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.ksysWrite fd buf count
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (ksysWrite_sameWGKernel fd buf count).wp P

theorem vfsRead_sameWGKernel (fid : FileId) (count : Nat) (pos : Option Int) : SameWGKernel (Leanux.vfsRead fid count pos) := by
  frame_wg [Leanux.vfsRead] using [fopsOf_spec, getFile_spec, newSyncRead_spec, rwVerifyArea_spec]

theorem vfsRead_spec (P : WGKernelView → Prop) (fid : FileId) (count : Nat) (pos : Option Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.vfsRead fid count pos
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (vfsRead_sameWGKernel fid count pos).wp P

theorem anonInodeGetfile_sameWGKernel (fopId : FopsId) (priv : PrivateData) (flags : UInt32) : SameWGKernel (Leanux.anonInodeGetfile fopId priv flags) := by
  frame_wg [Leanux.anonInodeGetfile] using [anonInodeGetfileImpl_spec]

theorem anonInodeGetfile_spec (P : WGKernelView → Prop) (fopId : FopsId) (priv : PrivateData) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.anonInodeGetfile fopId priv flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (anonInodeGetfile_sameWGKernel fopId priv flags).wp P

theorem doPipeFlags_sameWGKernel (flags : UInt32) : SameWGKernel (Leanux.doPipeFlags flags) := by
  frame_wg [Leanux.doPipeFlags] using [createPipeFiles_spec, fput_spec, getFile_spec, getUnusedFdFlags_spec, putUnusedFd_spec, setFile_spec]

theorem doPipeFlags_spec (P : WGKernelView → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.doPipeFlags flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doPipeFlags_sameWGKernel flags).wp P

theorem fputSync_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.fputSync fid) := by
  frame_wg [Leanux.fputSync] using [fputFinal_spec, getFile_spec, setFile_spec]

theorem fputSync_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fputSync fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fputSync_sameWGKernel fid).wp P

theorem ksysRead_sameWGKernel (fd : Nat) (count : Nat) : SameWGKernel (Leanux.ksysRead fd count) := by
  frame_wg [Leanux.ksysRead] using [fdgetPos_spec, fdputPos_spec, filePpos_spec, getFile_spec, setFile_spec, vfsRead_spec]

theorem ksysRead_spec (P : WGKernelView → Prop) (fd : Nat) (count : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.ksysRead fd count
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (ksysRead_sameWGKernel fd count).wp P

theorem sysDup_sameWGKernel (fildes : Nat) : SameWGKernel (Leanux.sysDup fildes) := by
  frame_wg [Leanux.sysDup] using [fdInstall_spec, fgetRaw_spec, fput_spec, getUnusedFdFlags_spec]

theorem sysDup_spec (P : WGKernelView → Prop) (fildes : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.sysDup fildes
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysDup_sameWGKernel fildes).wp P

theorem sysFcntl_sameWGKernel (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) : SameWGKernel (Leanux.sysFcntl fd cmd arg) := by
  frame_wg [Leanux.sysFcntl] using [doFcntl_spec, fdgetRaw_spec, fdput_spec, getFile_spec]

theorem sysFcntl_spec (P : WGKernelView → Prop) (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.sysFcntl fd cmd arg
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysFcntl_sameWGKernel fd cmd arg).wp P

theorem doEventfd_sameWGKernel (count : UInt32) (flags : UInt32) : SameWGKernel (Leanux.doEventfd count flags) := by
  frame_wg [Leanux.doEventfd] using [anonInodeGetfile_spec, eventfdFreeCtx_spec, fdInstall_spec, getCtx_spec, getFile_spec, getUnusedFdFlags_spec, hiddenAlloc_spec, idaAlloc_spec, putUnusedFd_spec, setCtx_spec, setFile_spec]

theorem doEventfd_spec (P : WGKernelView → Prop) (count : UInt32) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.doEventfd count flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doEventfd_sameWGKernel count flags).wp P

theorem doPipe2_sameWGKernel (flags : UInt32) : SameWGKernel (Leanux.doPipe2 flags) := by
  frame_wg [Leanux.doPipe2] using [doPipeFlags_spec, fdInstall_spec, fput_spec, putUnusedFd_spec]

theorem doPipe2_spec (P : WGKernelView → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.doPipe2 flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doPipe2_sameWGKernel flags).wp P

theorem sysClose_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.sysClose fd) := by
  frame_wg [Leanux.sysClose] using [fileCloseFd_spec, filpFlush_spec, fputSync_spec]

theorem sysClose_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.sysClose fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysClose_sameWGKernel fd).wp P

theorem sysEventfd2_sameWGKernel (count flags : UInt32) : SameWGKernel (Leanux.sysEventfd2 count flags) := by
  frame_wg [Leanux.sysEventfd2] using [doEventfd_spec]

theorem sysEventfd2_spec (P : WGKernelView → Prop) (count flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.sysEventfd2 count flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysEventfd2_sameWGKernel count flags).wp P

theorem sysPipe2_sameWGKernel (flags : UInt32) : SameWGKernel (Leanux.sysPipe2 flags) := by
  frame_wg [Leanux.sysPipe2] using [doPipe2_spec]

theorem sysPipe2_spec (P : WGKernelView → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.sysPipe2 flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sysPipe2_sameWGKernel flags).wp P

theorem taskWorkRun_sameWGKernel : SameWGKernel Leanux.taskWorkRun := by
  frame_wg [Leanux.taskWorkRun] using [fputFinal_spec]

theorem taskWorkRun_spec (P : WGKernelView → Prop) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.taskWorkRun
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := taskWorkRun_sameWGKernel.wp P

end Leanux.Proofs.Framing.FSFrames
