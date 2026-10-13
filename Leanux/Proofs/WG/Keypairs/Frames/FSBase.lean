import Leanux.Proofs.WG.Keypairs.SnapshotRules
import Leanux.Syscalls
import Leanux.Proofs.WG.Keypairs.Frames.PipeRead
import Leanux.Proofs.WG.Keypairs.Frames.WGBase

/-! Receive-snapshot contracts for filesystem primitives and their immediate
callers, including generic finite bit search and list predicates. -/

namespace Leanux.Proofs.WG.Keypairs.FSFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs Leanux.Proofs.Framing
open Leanux.Proofs.WG.Keypairs.KernelFrames Leanux.Proofs.WG.Keypairs.WGFrames
open Leanux.Proofs.WG.Keypairs.PipeFrames Leanux.Proofs.WG.Keypairs.PipeAux Leanux.Proofs.WG.Keypairs.WaitFrames

set_option maxHeartbeats 800000
set_option pp.structureInstances false

theorem allM_sameSnapshot (xs : List α) (f : α → M Bool)
    (hf : ∀ x, SameSnapshot (f x)) : SameSnapshot (xs.allM f) := by
  apply sameSnapshot_of_wp
  intro initial
  induction xs with
  | nil => mvcgen [List.allM_nil]
  | cons x xs ih =>
    have head_spec := (hf x).wp (fun s => s = initial)
    mvcgen [List.allM_cons, head_spec, ih]

theorem allM_spec (P : Snapshot → Prop) (xs : List α) (f : α → M Bool)
    (hf : ∀ x, SameSnapshot (f x)) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ xs.allM f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allM_sameSnapshot xs f hf).wp P

theorem findNextZeroBit_sameSnapshot (bit : Nat → M Bool) (size start : Nat)
    (hb : ∀ n, SameSnapshot (bit n)) : SameSnapshot (findNextZeroBit bit size start) := by
  have bit_spec (P : Snapshot → Prop) (n : Nat) := (hb n).wp P
  frame_same [findNextZeroBit] using [bit_spec]

theorem findNextZeroBit_spec (P : Snapshot → Prop) (bit : Nat → M Bool) (size start : Nat)
    (hb : ∀ n, SameSnapshot (bit n)) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ findNextZeroBit bit size start
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (findNextZeroBit_sameSnapshot bit size start hb).wp P

theorem accountPipeBuffers_spec (P : Snapshot → Prop) (old new : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.accountPipeBuffers old new
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.accountPipeBuffers_sameSnapshot old new).wp P

theorem copyPageFromIter_spec (P : Snapshot → Prop) (page : PageId) (offset bytes : Nat) (src : IovIter) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.copyPageFromIter page offset bytes src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.copyPageFromIter_sameSnapshot page offset bytes src).wp P

theorem getPipeBuf_spec (P : Snapshot → Prop) (pid : PipeId) (i : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getPipeBuf pid i
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.getPipeBuf_sameSnapshot pid i).wp P

theorem newPipePage_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.newPipePage
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.newPipePage_sameSnapshot ).wp P

theorem pipeBufConfirm_spec (P : Snapshot → Prop) (buf : PipeBuffer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipeBufConfirm buf
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.pipeBufConfirm_sameSnapshot buf).wp P

theorem pipeBufIdx_spec (P : Snapshot → Prop) (p : PipeInodeInfo) (slot : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipeBufIdx p slot
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.pipeBufIdx_sameSnapshot p slot).wp P

theorem pipeBufRelease_spec (P : Snapshot → Prop) (pid : PipeId) (i : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipeBufRelease pid i
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.pipeBufRelease_sameSnapshot pid i).wp P

theorem pipeRelease_spec (P : Snapshot → Prop) (ino : PipefsInodeId) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipeRelease ino fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.pipeRelease_sameSnapshot ino fid).wp P

theorem putPipePage_spec (P : Snapshot → Prop) (id : PageId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.putPipePage id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.putPipePage_sameSnapshot id).wp P

theorem setPipeBuf_spec (P : Snapshot → Prop) (pid : PipeId) (i : Nat) (b : PipeBuffer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setPipeBuf pid i b
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Leanux.Proofs.WG.Keypairs.PipeFrames.setPipeBuf_sameSnapshot pid i b).wp P

theorem copyPageToIter_spec (P : Snapshot → Prop) (page : PageId) (offset bytes cap : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ copyPageToIter page offset bytes cap
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (sameSnapshot_of_sameKernel (copyPageToIter_sameKernel page offset bytes cap)).wp P

theorem allocEmptyFile_sameSnapshot (flags : UInt32) : SameSnapshot (Leanux.allocEmptyFile flags) := by
  frame_same [Leanux.allocEmptyFile] using [hiddenAlloc_snapshot_spec, setFile_spec]

theorem allocEmptyFile_spec (P : Snapshot → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.allocEmptyFile flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allocEmptyFile_sameSnapshot flags).wp P

theorem allocFdtable_sameSnapshot (slotsWanted : Nat) : SameSnapshot (Leanux.allocFdtable slotsWanted) := by
  frame_same [Leanux.allocFdtable] using [hiddenAlloc_snapshot_spec]

theorem allocFdtable_spec (P : Snapshot → Prop) (slotsWanted : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.allocFdtable slotsWanted
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allocFdtable_sameSnapshot slotsWanted).wp P

theorem allocPathPseudo_sameSnapshot (inode : InodeId) : SameSnapshot (Leanux.allocPathPseudo inode) := by
  frame_same [Leanux.allocPathPseudo] using [getInode_spec, hiddenAlloc_snapshot_spec, setInode_spec]

theorem allocPathPseudo_spec (P : Snapshot → Prop) (inode : InodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.allocPathPseudo inode
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allocPathPseudo_sameSnapshot inode).wp P

theorem anonPipeBufRelease_sameSnapshot (pid : PipeId) (buf : PipeBuffer) : SameSnapshot (Leanux.anonPipeBufRelease pid buf) := by
  frame_same [Leanux.anonPipeBufRelease] using [getPage_spec, getPipe_spec, putPipePage_spec, setPipe_spec]

theorem anonPipeBufRelease_spec (P : Snapshot → Prop) (pid : PipeId) (buf : PipeBuffer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.anonPipeBufRelease pid buf
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (anonPipeBufRelease_sameSnapshot pid buf).wp P

theorem clearCloseOnExecBit_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.clearCloseOnExecBit fd) := by
  frame_same [Leanux.clearCloseOnExecBit] using [fdtCloexec_spec, setFdtCloexec_spec]

theorem clearCloseOnExecBit_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.clearCloseOnExecBit fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (clearCloseOnExecBit_sameSnapshot fd).wp P

theorem clearOpenFd_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.clearOpenFd fd) := by
  frame_same [Leanux.clearOpenFd] using [setFdtOpen_spec]

theorem clearOpenFd_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.clearOpenFd fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (clearOpenFd_sameSnapshot fd).wp P

theorem copyFdtable_sameSnapshot (nfdt ofdt : Fdtable) : SameSnapshot (Leanux.copyFdtable nfdt ofdt) := by
  frame_same [Leanux.copyFdtable] using []

theorem copyFdtable_spec (P : Snapshot → Prop) (nfdt ofdt : Fdtable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.copyFdtable nfdt ofdt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (copyFdtable_sameSnapshot nfdt ofdt).wp P

theorem copyPipeBufs_sameSnapshot (dst src : Array PipeBuffer) (dstOff srcOff len : Nat) : SameSnapshot (Leanux.copyPipeBufs dst src dstOff srcOff len) := by
  frame_same [Leanux.copyPipeBufs] using []

theorem copyPipeBufs_spec (P : Snapshot → Prop) (dst src : Array PipeBuffer) (dstOff srcOff len : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.copyPipeBufs dst src dstOff srcOff len
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (copyPipeBufs_sameSnapshot dst src dstOff srcOff len).wp P

theorem eventfdCtxDoRead_sameSnapshot (id : CtxId) : SameSnapshot (Leanux.eventfdCtxDoRead id) := by
  frame_same [Leanux.eventfdCtxDoRead] using [getCtx_spec, setCtx_spec]

theorem eventfdCtxDoRead_spec (P : Snapshot → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventfdCtxDoRead id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventfdCtxDoRead_sameSnapshot id).wp P

theorem eventfdCtxOf_sameSnapshot (file : File) : SameSnapshot (Leanux.eventfdCtxOf file) := by
  frame_same [Leanux.eventfdCtxOf] using []

theorem eventfdCtxOf_spec (P : Snapshot → Prop) (file : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventfdCtxOf file
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventfdCtxOf_sameSnapshot file).wp P

theorem eventfdFreeCtx_sameSnapshot (id : CtxId) : SameSnapshot (Leanux.eventfdFreeCtx id) := by
  frame_same [Leanux.eventfdFreeCtx] using [freeCtx_spec, getCtx_spec]

theorem eventfdFreeCtx_spec (P : Snapshot → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventfdFreeCtx id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventfdFreeCtx_sameSnapshot id).wp P

theorem fdInstall_sameSnapshot (fd : Nat) (fid : FileId) : SameSnapshot (Leanux.fdInstall fd fid) := by
  frame_same [Leanux.fdInstall] using [fdtSlot_spec, getFile_spec, setFdtSlot_spec]

theorem fdInstall_spec (P : Snapshot → Prop) (fd : Nat) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fdInstall fd fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fdInstall_sameSnapshot fd fid).wp P

theorem fileFree_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.fileFree fid) := by
  frame_same [Leanux.fileFree] using [freeFile_spec, getFile_spec]

theorem fileFree_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fileFree fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileFree_sameSnapshot fid).wp P

theorem filePpos_sameSnapshot (f : File) : SameSnapshot (Leanux.filePpos f) := by
  frame_same [Leanux.filePpos] using []

theorem filePpos_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.filePpos f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (filePpos_sameSnapshot f).wp P

theorem filesLookupFdRaw_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.filesLookupFdRaw fd) := by
  frame_same [Leanux.filesLookupFdRaw] using [fdtSlot_spec]

theorem filesLookupFdRaw_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.filesLookupFdRaw fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (filesLookupFdRaw_sameSnapshot fd).wp P

theorem fopWriteIter_sameSnapshot (iocb : Kiocb) («from» : IovIter) (which : Option FopsId) : SameSnapshot (Leanux.fopWriteIter iocb «from» which) := by
  cases which with
  | none => frame_same [Leanux.fopWriteIter] using [pipeWrite_spec]
  | some k => cases k <;> frame_same [Leanux.fopWriteIter] using [pipeWrite_spec]

theorem fopWriteIter_spec (P : Snapshot → Prop) (iocb : Kiocb) («from» : IovIter) (which : Option FopsId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fopWriteIter iocb «from» which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fopWriteIter_sameSnapshot iocb «from» which).wp P

theorem fopsOf_sameSnapshot  (which : Option FopsId) : SameSnapshot (Leanux.fopsOf which) := by
  cases which with
  | none => frame_same [Leanux.fopsOf] using []
  | some k => cases k <;> frame_same [Leanux.fopsOf] using []

theorem fopsOf_spec (P : Snapshot → Prop)  (which : Option FopsId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fopsOf which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fopsOf_sameSnapshot which).wp P

theorem fullWord_sameSnapshot (fdt : Fdtable) (word : Nat) : SameSnapshot (Leanux.fullWord fdt word) := by
  unfold Leanux.fullWord
  exact allM_sameSnapshot _ _ (fun _ => fdtOpen_sameSnapshot _ _)

theorem fullWord_spec (P : Snapshot → Prop) (fdt : Fdtable) (word : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fullWord fdt word
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fullWord_sameSnapshot fdt word).wp P

theorem getCloseOnExec_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.getCloseOnExec fd) := by
  frame_same [Leanux.getCloseOnExec] using [fdtCloexec_spec]

theorem getCloseOnExec_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getCloseOnExec fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getCloseOnExec_sameSnapshot fd).wp P

theorem getCurrentUser_sameSnapshot  : SameSnapshot (Leanux.getCurrentUser ) := by
  frame_same [Leanux.getCurrentUser] using [refcountIncGuestWide_spec]

theorem getCurrentUser_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getCurrentUser
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getCurrentUser_sameSnapshot ).wp P

theorem getFileRef_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.getFileRef fid) := by
  frame_same [Leanux.getFileRef] using [getFile_spec, setFile_spec]

theorem getFileRef_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getFileRef fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getFileRef_sameSnapshot fid).wp P

theorem getPipeInfo_sameSnapshot (f : File) : SameSnapshot (Leanux.getPipeInfo f) := by
  frame_same [Leanux.getPipeInfo] using []

theorem getPipeInfo_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getPipeInfo f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getPipeInfo_sameSnapshot f).wp P

theorem idaAlloc_sameSnapshot  : SameSnapshot (Leanux.idaAlloc ) := by
  frame_same [Leanux.idaAlloc] using []

theorem idaAlloc_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.idaAlloc
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (idaAlloc_sameSnapshot ).wp P

theorem inodeFileType_sameSnapshot  (which : Option InodeId) : SameSnapshot (Leanux.inodeFileType which) := by
  cases which with
  | none => frame_same [Leanux.inodeFileType] using [getInode_spec]
  | some k => cases k <;> frame_same [Leanux.inodeFileType] using [getInode_spec]

theorem inodeFileType_spec (P : Snapshot → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.inodeFileType which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeFileType_sameSnapshot which).wp P

theorem inodeFlags_sameSnapshot  (which : Option InodeId) : SameSnapshot (Leanux.inodeFlags which) := by
  cases which with
  | none => frame_same [Leanux.inodeFlags] using [getInode_spec]
  | some k => cases k <;> frame_same [Leanux.inodeFlags] using [getInode_spec]

theorem inodeFlags_spec (P : Snapshot → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.inodeFlags which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeFlags_sameSnapshot which).wp P

theorem inodeIsChr_sameSnapshot  (which : Option InodeId) : SameSnapshot (Leanux.inodeIsChr which) := by
  cases which with
  | none => frame_same [Leanux.inodeIsChr] using [getInode_spec]
  | some k => cases k <;> frame_same [Leanux.inodeIsChr] using [getInode_spec]

theorem inodeIsChr_spec (P : Snapshot → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.inodeIsChr which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeIsChr_sameSnapshot which).wp P

theorem inodeIsReg_sameSnapshot  (which : Option InodeId) : SameSnapshot (Leanux.inodeIsReg which) := by
  cases which with
  | none => frame_same [Leanux.inodeIsReg] using [getInode_spec]
  | some k => cases k <;> frame_same [Leanux.inodeIsReg] using [getInode_spec]

theorem inodeIsReg_spec (P : Snapshot → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.inodeIsReg which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeIsReg_sameSnapshot which).wp P

theorem inodeReadcountDec_sameSnapshot  (which : Option InodeId) : SameSnapshot (Leanux.inodeReadcountDec which) := by
  cases which with
  | none => frame_same [Leanux.inodeReadcountDec] using [getInode_spec, setInode_spec]
  | some k => cases k <;> frame_same [Leanux.inodeReadcountDec] using [getInode_spec, setInode_spec]

theorem inodeReadcountDec_spec (P : Snapshot → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.inodeReadcountDec which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeReadcountDec_sameSnapshot which).wp P

theorem inodeReadcountInc_sameSnapshot  (which : Option InodeId) : SameSnapshot (Leanux.inodeReadcountInc which) := by
  cases which with
  | none => frame_same [Leanux.inodeReadcountInc] using [getInode_spec, setInode_spec]
  | some k => cases k <;> frame_same [Leanux.inodeReadcountInc] using [getInode_spec, setInode_spec]

theorem inodeReadcountInc_spec (P : Snapshot → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.inodeReadcountInc which
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeReadcountInc_sameSnapshot which).wp P

theorem iocbFlags_sameSnapshot (fFlags : UInt32) : SameSnapshot (Leanux.iocbFlags fFlags) := by
  frame_same [Leanux.iocbFlags] using []

theorem iocbFlags_spec (P : Snapshot → Prop) (fFlags : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.iocbFlags fFlags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (iocbFlags_sameSnapshot fFlags).wp P

theorem iputPipefs_sameSnapshot (id : PipefsInodeId) : SameSnapshot (Leanux.iputPipefs id) := by
  frame_same [Leanux.iputPipefs] using [getInode_spec, setInode_spec]

theorem iputPipefs_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.iputPipefs id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (iputPipefs_sameSnapshot id).wp P

theorem newInodePseudo_sameSnapshot  : SameSnapshot (Leanux.newInodePseudo ) := by
  frame_same [Leanux.newInodePseudo] using [envOk_spec, setInode_spec]

theorem newInodePseudo_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.newInodePseudo
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (newInodePseudo_sameSnapshot ).wp P

theorem pipeIsUnprivilegedUser_sameSnapshot  : SameSnapshot (Leanux.pipeIsUnprivilegedUser ) := by
  frame_same [Leanux.pipeIsUnprivilegedUser] using []

theorem pipeIsUnprivilegedUser_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipeIsUnprivilegedUser
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeIsUnprivilegedUser_sameSnapshot ).wp P

theorem pipeUpdateTail_sameSnapshot (pid : PipeId) (i : Nat) (tail : UInt32) : SameSnapshot (Leanux.pipeUpdateTail pid i tail) := by
  frame_same [Leanux.pipeUpdateTail] using [getPipe_spec, pipeBufRelease_spec, setPipe_spec]

theorem pipeUpdateTail_spec (P : Snapshot → Prop) (pid : PipeId) (i : Nat) (tail : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipeUpdateTail pid i tail
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeUpdateTail_sameSnapshot pid i tail).wp P

theorem roundPipeSize_sameSnapshot (size : Nat) : SameSnapshot (Leanux.roundPipeSize size) := by
  frame_same [Leanux.roundPipeSize] using []

theorem roundPipeSize_spec (P : Snapshot → Prop) (size : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.roundPipeSize size
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (roundPipeSize_sameSnapshot size).wp P

theorem rwVerifyArea_sameSnapshot (ppos : Option Int) (count : Nat) : SameSnapshot (Leanux.rwVerifyArea ppos count) := by
  frame_same [Leanux.rwVerifyArea] using []

theorem rwVerifyArea_spec (P : Snapshot → Prop) (ppos : Option Int) (count : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.rwVerifyArea ppos count
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (rwVerifyArea_sameSnapshot ppos count).wp P

theorem setCloseOnExecBit_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.setCloseOnExecBit fd) := by
  frame_same [Leanux.setCloseOnExecBit] using [setFdtCloexec_spec]

theorem setCloseOnExecBit_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setCloseOnExecBit fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setCloseOnExecBit_sameSnapshot fd).wp P

theorem simpleInodeInitTs_sameSnapshot (id : PipefsInodeId) : SameSnapshot (Leanux.simpleInodeInitTs id) := by
  frame_same [Leanux.simpleInodeInitTs] using [getInode_spec, inodeSetCtimeCurrent_spec, setInode_spec]

theorem simpleInodeInitTs_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.simpleInodeInitTs id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (simpleInodeInitTs_sameSnapshot id).wp P

theorem streamOpen_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.streamOpen fid) := by
  frame_same [Leanux.streamOpen] using [getFile_spec, setFile_spec]

theorem streamOpen_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.streamOpen fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (streamOpen_sameSnapshot fid).wp P

theorem tooManyPipeBuffersHard_sameSnapshot (userBufs : Nat) : SameSnapshot (Leanux.tooManyPipeBuffersHard userBufs) := by
  frame_same [Leanux.tooManyPipeBuffersHard] using []

theorem tooManyPipeBuffersHard_spec (P : Snapshot → Prop) (userBufs : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.tooManyPipeBuffersHard userBufs
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (tooManyPipeBuffersHard_sameSnapshot userBufs).wp P

theorem tooManyPipeBuffersSoft_sameSnapshot (userBufs : Nat) : SameSnapshot (Leanux.tooManyPipeBuffersSoft userBufs) := by
  frame_same [Leanux.tooManyPipeBuffersSoft] using []

theorem tooManyPipeBuffersSoft_spec (P : Snapshot → Prop) (userBufs : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.tooManyPipeBuffersSoft userBufs
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (tooManyPipeBuffersSoft_sameSnapshot userBufs).wp P

theorem pipefsInodeOf_sameSnapshot (f : File) (what : String) : SameSnapshot ((pinned_const _private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf) f what) := by
  frame_same [_private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf] using []

theorem pipefsInodeOf_spec (P : Snapshot → Prop) (f : File) (what : String) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf) f what
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipefsInodeOf_sameSnapshot f what).wp P

theorem allocPipeInfo_sameSnapshot  : SameSnapshot (Leanux.allocPipeInfo ) := by
  frame_same [Leanux.allocPipeInfo] using [accountPipeBuffers_spec, getCurrentUser_spec, hiddenAlloc_snapshot_spec, pipeIsUnprivilegedUser_spec, setPipe_spec, tooManyPipeBuffersHard_spec, tooManyPipeBuffersSoft_spec]

theorem allocPipeInfo_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.allocPipeInfo
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (allocPipeInfo_sameSnapshot ).wp P

theorem dputPipefs_sameSnapshot (id : PipefsInodeId) : SameSnapshot (Leanux.dputPipefs id) := by
  frame_same [Leanux.dputPipefs] using [getInode_spec, iputPipefs_spec, setInode_spec]

theorem dputPipefs_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.dputPipefs id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dputPipefs_sameSnapshot id).wp P

theorem eventfdCtxPut_sameSnapshot (id : CtxId) : SameSnapshot (Leanux.eventfdCtxPut id) := by
  frame_same [Leanux.eventfdCtxPut] using [eventfdFreeCtx_spec, getCtx_spec, refcountDecAndTest_spec, setCtx_spec]

theorem eventfdCtxPut_spec (P : Snapshot → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventfdCtxPut id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventfdCtxPut_sameSnapshot id).wp P

theorem eventfdRead_sameSnapshot (iocb : Kiocb) (iterCount : Nat) : SameSnapshot (Leanux.eventfdRead iocb iterCount) := by
  frame_same [Leanux.eventfdRead] using [eventfdCtxDoRead_spec, eventfdCtxOf_spec, getCtx_spec, getFile_spec,
    waitqueueActive_spec, wakeUpLockedPoll_spec]

theorem eventfdRead_spec (P : Snapshot → Prop) (iocb : Kiocb) (iterCount : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventfdRead iocb iterCount
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventfdRead_sameSnapshot iocb iterCount).wp P

theorem eventfdWrite_sameSnapshot (fid : FileId) (buf : ByteArray) (count : Nat) : SameSnapshot (Leanux.eventfdWrite fid buf count) := by
  unfold Leanux.eventfdWrite
  repeat' first
    | (snapshot_head Leanux.eventfdCtxOf; with_reducible exact @eventfdCtxOf_sameSnapshot _)
    | (snapshot_head Leanux.getCtx; with_reducible exact @getCtx_sameSnapshot _)
    | (snapshot_head Leanux.getFile; with_reducible exact @getFile_sameSnapshot _)
    | (snapshot_head Leanux.setCtx; with_reducible exact @setCtx_sameSnapshot _ _)
    | (snapshot_head Leanux.wakeUpLockedPoll; with_reducible exact @wakeUpLockedPoll_sameSnapshot _ _)
    | (snapshot_head Leanux.waitqueueActive; with_reducible exact @waitqueueActive_sameSnapshot _)
    | (snapshot_head Leanux.getK; with_reducible exact @getK_sameSnapshot)
    | (snapshot_head Leanux.branch; with_reducible exact @branch_sameSnapshot _ _)
    | (snapshot_head Leanux.branchCmp; with_reducible exact @branchCmp_sameSnapshot _ _ _ _)
    | (snapshot_head Leanux.invariant; with_reducible exact @invariant_sameSnapshot _ _)
    | (snapshot_head Leanux.unsupported; with_reducible exact @unsupported_sameSnapshot _ _)
    | snapshot_step

theorem eventfdWrite_spec (P : Snapshot → Prop) (fid : FileId) (buf : ByteArray) (count : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.eventfdWrite fid buf count
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (eventfdWrite_sameSnapshot fid buf count).wp P

theorem expandFdtable_sameSnapshot (nr : Nat) : SameSnapshot (Leanux.expandFdtable nr) := by
  frame_same [Leanux.expandFdtable] using [allocFdtable_spec, copyFdtable_spec]

theorem expandFdtable_spec (P : Snapshot → Prop) (nr : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.expandFdtable nr
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (expandFdtable_sameSnapshot nr).wp P

theorem fgetLight_sameSnapshot (fd : Nat) (mask : UInt32) : SameSnapshot (Leanux.fgetLight fd mask) := by
  frame_same [Leanux.fgetLight] using [filesLookupFdRaw_spec, getFile_spec]

theorem fgetLight_spec (P : Snapshot → Prop) (fd : Nat) (mask : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fgetLight fd mask
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fgetLight_sameSnapshot fd mask).wp P

theorem fileEndWrite_sameSnapshot (f : File) : SameSnapshot (Leanux.fileEndWrite f) := by
  frame_same [Leanux.fileEndWrite] using [inodeIsReg_spec]

theorem fileEndWrite_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fileEndWrite f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileEndWrite_sameSnapshot f).wp P

theorem fileInitPath_sameSnapshot (fid : FileId) (fopId : FopsId) (inode : InodeId) : SameSnapshot (Leanux.fileInitPath fid fopId inode) := by
  frame_same [Leanux.fileInitPath] using [fopsOf_spec, getFile_spec, inodeReadcountInc_spec, iocbFlags_spec, setFile_spec]

theorem fileInitPath_spec (P : Snapshot → Prop) (fid : FileId) (fopId : FopsId) (inode : InodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fileInitPath fid fopId inode
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileInitPath_sameSnapshot fid fopId inode).wp P

theorem fileStartWrite_sameSnapshot (f : File) : SameSnapshot (Leanux.fileStartWrite f) := by
  frame_same [Leanux.fileStartWrite] using [inodeIsReg_spec]

theorem fileStartWrite_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fileStartWrite f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileStartWrite_sameSnapshot f).wp P

theorem filpFlush_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.filpFlush fid) := by
  frame_same [Leanux.filpFlush] using [fopsOf_spec, getFile_spec]

theorem filpFlush_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.filpFlush fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (filpFlush_sameSnapshot fid).wp P

theorem findNextFd_sameSnapshot (fdt : Fdtable) (start : Nat) : SameSnapshot (Leanux.findNextFd fdt start) := by
  have word_spec (P : Snapshot → Prop) (fd : Fdtable) (size start : Nat) :=
    (findNextZeroBit_sameSnapshot (fullWord fd) size start
      (fun i => fullWord_sameSnapshot fd i)).wp P
  have fd_spec (P : Snapshot → Prop) (fd : Fdtable) (size start : Nat) :=
    (findNextZeroBit_sameSnapshot (fdtOpen fd) size start
      (fun i => fdtOpen_sameSnapshot fd i)).wp P
  frame_same [Leanux.findNextFd] using [word_spec, fd_spec]

theorem findNextFd_spec (P : Snapshot → Prop) (fdt : Fdtable) (start : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.findNextFd fdt start
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (findNextFd_sameSnapshot fdt start).wp P

theorem fput_sameSnapshot (fid : FileId) : SameSnapshot (Leanux.fput fid) := by
  frame_same [Leanux.fput] using [fileFree_spec, getFile_spec, setFile_spec]

theorem fput_spec (P : Snapshot → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fput fid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fput_sameSnapshot fid).wp P

theorem newSyncWrite_sameSnapshot (fid : FileId) (buf : ByteArray) (len : Nat) (ppos : Option Int) : SameSnapshot (Leanux.newSyncWrite fid buf len ppos) := by
  frame_same [Leanux.newSyncWrite] using [fopWriteIter_spec, getFile_spec]

theorem newSyncWrite_spec (P : Snapshot → Prop) (fid : FileId) (buf : ByteArray) (len : Nat) (ppos : Option Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.newSyncWrite fid buf len ppos
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (newSyncWrite_sameSnapshot fid buf len ppos).wp P

theorem pipeResizeRing_sameSnapshot (pid : PipeId) (nrSlots : Nat) : SameSnapshot (Leanux.pipeResizeRing pid nrSlots) := by
  frame_same [Leanux.pipeResizeRing] using [copyPipeBufs_spec, envOk_spec, getPipe_spec, setPipe_spec,
    wakeUpInterruptible_spec]

theorem pipeResizeRing_spec (P : Snapshot → Prop) (pid : PipeId) (nrSlots : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.pipeResizeRing pid nrSlots
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeResizeRing_sameSnapshot pid nrSlots).wp P

theorem putFileAccess_sameSnapshot (f : File) : SameSnapshot (Leanux.putFileAccess f) := by
  frame_same [Leanux.putFileAccess] using [inodeReadcountDec_spec]

theorem putFileAccess_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.putFileAccess f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (putFileAccess_sameSnapshot f).wp P

theorem putUnusedFdLocked_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.putUnusedFdLocked fd) := by
  frame_same [Leanux.putUnusedFdLocked] using [clearOpenFd_spec]

theorem putUnusedFdLocked_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.putUnusedFdLocked fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (putUnusedFdLocked_sameSnapshot fd).wp P

theorem setCloseOnExec_sameSnapshot (fd : Nat) (flag : Bool) : SameSnapshot (Leanux.setCloseOnExec fd flag) := by
  frame_same [Leanux.setCloseOnExec] using [clearCloseOnExecBit_spec, setCloseOnExecBit_spec]

theorem setCloseOnExec_spec (P : Snapshot → Prop) (fd : Nat) (flag : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setCloseOnExec fd flag
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setCloseOnExec_sameSnapshot fd flag).wp P

theorem setOpenFd_sameSnapshot (fd : Nat) : SameSnapshot (Leanux.setOpenFd fd) := by
  frame_same [Leanux.setOpenFd] using [fullWord_spec, setFdtOpen_spec]

theorem setOpenFd_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setOpenFd fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setOpenFd_sameSnapshot fd).wp P

theorem setfl_sameSnapshot (fid : FileId) (arg : UInt32) : SameSnapshot (Leanux.setfl fid arg) := by
  frame_same [Leanux.setfl] using [fopsOf_spec, getFile_spec, inodeFileType_spec, inodeFlags_spec, iocbFlags_spec, setFile_spec]

theorem setfl_spec (P : Snapshot → Prop) (fid : FileId) (arg : UInt32) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setfl fid arg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setfl_sameSnapshot fid arg).wp P

end Leanux.Proofs.WG.Keypairs.FSFrames
