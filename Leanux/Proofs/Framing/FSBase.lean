import Leanux.Proofs.Framing.Control
import Leanux.Syscalls
import Leanux.Proofs.Framing.PipeRead

/-! Full WireGuard kernel contracts for filesystem primitives and their immediate
callers, including generic finite bit search and list predicates. -/

namespace Leanux.Proofs.Framing.FSFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.Framing.KernelFrames
open Leanux.Proofs.Framing.PipeFrames Leanux.Proofs.Framing.PipeAux Leanux.Proofs.Framing.WaitFrames

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-- Callback framing is projection-parametric: legacy clients need only their
own weaker view, not preservation of the full WireGuard kernel. -/
theorem allM_sameView {σ : Type} (view : World → σ) (xs : List α) (f : α → M Bool)
    (hf : ∀ x, SameView view (f x)) : SameView view (xs.allM f) := by
  apply SameView.of_wp
  intro initial
  induction xs with
  | nil => mvcgen [List.allM_nil]
  | cons x xs ih =>
    have head_spec := (hf x).wp (fun s => s = initial)
    mvcgen [List.allM_cons, head_spec, ih]

theorem allM_sameWGKernel (xs : List α) (f : α → M Bool)
    (hf : ∀ x, SameWGKernel (f x)) : SameWGKernel (xs.allM f) :=
  allM_sameView wgKernelView xs f hf

theorem allM_spec (P : WGKernelView → Prop) (xs : List α) (f : α → M Bool)
    (hf : ∀ x, SameWGKernel (f x)) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ xs.allM f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (allM_sameWGKernel xs f hf).wp P

theorem findNextZeroBit_sameView {σ : Type} (view : World → σ) (bit : Nat → M Bool) (size start : Nat)
    (hb : ∀ n, SameView view (bit n)) : SameView view (findNextZeroBit bit size start) := by
  apply SameView.of_wp
  intro initial
  have bit_spec (n : Nat) := (hb n).wp (fun s => s = initial)
  have list_spec (α β : Type) := list_view_spec view (α := α) (β := β) (fun s => s = initial)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, findNextZeroBit, list_spec, bit_spec]

theorem findNextZeroBit_sameWGKernel (bit : Nat → M Bool) (size start : Nat)
    (hb : ∀ n, SameWGKernel (bit n)) : SameWGKernel (findNextZeroBit bit size start) :=
  findNextZeroBit_sameView wgKernelView bit size start hb

theorem findNextZeroBit_spec (P : WGKernelView → Prop) (bit : Nat → M Bool) (size start : Nat)
    (hb : ∀ n, SameWGKernel (bit n)) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ findNextZeroBit bit size start
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (findNextZeroBit_sameWGKernel bit size start hb).wp P

theorem accountPipeBuffers_spec (P : WGKernelView → Prop) (old new : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.accountPipeBuffers old new
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.accountPipeBuffers_sameWGKernel old new).wp P

theorem copyPageFromIter_spec (P : WGKernelView → Prop) (page : PageId) (offset bytes : Nat) (src : IovIter) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.copyPageFromIter page offset bytes src
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.copyPageFromIter_sameWGKernel page offset bytes src).wp P

theorem getPipeBuf_spec (P : WGKernelView → Prop) (pid : PipeId) (i : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getPipeBuf pid i
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.getPipeBuf_sameWGKernel pid i).wp P

theorem newPipePage_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.newPipePage
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.newPipePage_sameWGKernel ).wp P

theorem pipeBufConfirm_spec (P : WGKernelView → Prop) (buf : PipeBuffer) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipeBufConfirm buf
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.pipeBufConfirm_sameWGKernel buf).wp P

theorem pipeBufIdx_spec (P : WGKernelView → Prop) (p : PipeInodeInfo) (slot : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipeBufIdx p slot
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.pipeBufIdx_sameWGKernel p slot).wp P

theorem pipeBufRelease_spec (P : WGKernelView → Prop) (pid : PipeId) (i : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipeBufRelease pid i
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.pipeBufRelease_sameWGKernel pid i).wp P

theorem pipeRelease_spec (P : WGKernelView → Prop) (ino : PipefsInodeId) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipeRelease ino fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.pipeRelease_sameWGKernel ino fid).wp P

theorem putPipePage_spec (P : WGKernelView → Prop) (id : PageId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.putPipePage id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.putPipePage_sameWGKernel id).wp P

theorem setPipeBuf_spec (P : WGKernelView → Prop) (pid : PipeId) (i : Nat) (b : PipeBuffer) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setPipeBuf pid i b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (Leanux.Proofs.Framing.PipeFrames.setPipeBuf_sameWGKernel pid i b).wp P

theorem copyPageToIter_spec (P : WGKernelView → Prop) (page : PageId) (offset bytes cap : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ copyPageToIter page offset bytes cap
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (sameWGKernel_of_sameKernel (copyPageToIter_sameKernel page offset bytes cap)).wp P

theorem allocEmptyFile_sameWGKernel (flags : UInt32) : SameWGKernel (Leanux.allocEmptyFile flags) := by
  frame_wg [Leanux.allocEmptyFile] using [hiddenAlloc_spec, setFile_spec]

theorem allocEmptyFile_spec (P : WGKernelView → Prop) (flags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.allocEmptyFile flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (allocEmptyFile_sameWGKernel flags).wp P

theorem allocFdtable_sameWGKernel (slotsWanted : Nat) : SameWGKernel (Leanux.allocFdtable slotsWanted) := by
  frame_wg [Leanux.allocFdtable] using [hiddenAlloc_spec]

theorem allocFdtable_spec (P : WGKernelView → Prop) (slotsWanted : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.allocFdtable slotsWanted
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (allocFdtable_sameWGKernel slotsWanted).wp P

theorem allocPathPseudo_sameWGKernel (inode : InodeId) : SameWGKernel (Leanux.allocPathPseudo inode) := by
  frame_wg [Leanux.allocPathPseudo] using [getInode_spec, hiddenAlloc_spec, setInode_spec]

theorem allocPathPseudo_spec (P : WGKernelView → Prop) (inode : InodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.allocPathPseudo inode
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (allocPathPseudo_sameWGKernel inode).wp P

theorem anonPipeBufRelease_sameWGKernel (pid : PipeId) (buf : PipeBuffer) : SameWGKernel (Leanux.anonPipeBufRelease pid buf) := by
  frame_wg [Leanux.anonPipeBufRelease] using [getPage_spec, getPipe_spec, putPipePage_spec, setPipe_spec]

theorem anonPipeBufRelease_spec (P : WGKernelView → Prop) (pid : PipeId) (buf : PipeBuffer) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.anonPipeBufRelease pid buf
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (anonPipeBufRelease_sameWGKernel pid buf).wp P

theorem clearCloseOnExecBit_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.clearCloseOnExecBit fd) := by
  frame_wg [Leanux.clearCloseOnExecBit] using [fdtCloexec_spec, setFdtCloexec_spec]

theorem clearCloseOnExecBit_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.clearCloseOnExecBit fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (clearCloseOnExecBit_sameWGKernel fd).wp P

theorem clearOpenFd_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.clearOpenFd fd) := by
  frame_wg [Leanux.clearOpenFd] using [setFdtOpen_spec]

theorem clearOpenFd_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.clearOpenFd fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (clearOpenFd_sameWGKernel fd).wp P

theorem copyFdtable_sameWGKernel (nfdt ofdt : Fdtable) : SameWGKernel (Leanux.copyFdtable nfdt ofdt) := by
  frame_wg [Leanux.copyFdtable] using []

theorem copyFdtable_spec (P : WGKernelView → Prop) (nfdt ofdt : Fdtable) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.copyFdtable nfdt ofdt
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (copyFdtable_sameWGKernel nfdt ofdt).wp P

theorem copyPipeBufs_sameWGKernel (dst src : Array PipeBuffer) (dstOff srcOff len : Nat) : SameWGKernel (Leanux.copyPipeBufs dst src dstOff srcOff len) := by
  frame_wg [Leanux.copyPipeBufs] using []

theorem copyPipeBufs_spec (P : WGKernelView → Prop) (dst src : Array PipeBuffer) (dstOff srcOff len : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.copyPipeBufs dst src dstOff srcOff len
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (copyPipeBufs_sameWGKernel dst src dstOff srcOff len).wp P

theorem eventfdCtxDoRead_sameWGKernel (id : CtxId) : SameWGKernel (Leanux.eventfdCtxDoRead id) := by
  frame_wg [Leanux.eventfdCtxDoRead] using [getCtx_spec, setCtx_spec]

theorem eventfdCtxDoRead_spec (P : WGKernelView → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.eventfdCtxDoRead id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (eventfdCtxDoRead_sameWGKernel id).wp P

theorem eventfdCtxOf_sameWGKernel (file : File) : SameWGKernel (Leanux.eventfdCtxOf file) := by
  frame_wg [Leanux.eventfdCtxOf] using []

theorem eventfdCtxOf_spec (P : WGKernelView → Prop) (file : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.eventfdCtxOf file
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (eventfdCtxOf_sameWGKernel file).wp P

theorem eventfdFreeCtx_sameWGKernel (id : CtxId) : SameWGKernel (Leanux.eventfdFreeCtx id) := by
  frame_wg [Leanux.eventfdFreeCtx] using [freeCtx_spec, getCtx_spec]

theorem eventfdFreeCtx_spec (P : WGKernelView → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.eventfdFreeCtx id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (eventfdFreeCtx_sameWGKernel id).wp P

theorem fdInstall_sameWGKernel (fd : Nat) (fid : FileId) : SameWGKernel (Leanux.fdInstall fd fid) := by
  frame_wg [Leanux.fdInstall] using [fdtSlot_spec, getFile_spec, setFdtSlot_spec]

theorem fdInstall_spec (P : WGKernelView → Prop) (fd : Nat) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fdInstall fd fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fdInstall_sameWGKernel fd fid).wp P

theorem fileFree_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.fileFree fid) :=
  (Framing.FSFileRefs.fileFree_sameWGKernel fid)

theorem fileFree_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fileFree fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fileFree_sameWGKernel fid).wp P

theorem filePpos_sameWGKernel (f : File) : SameWGKernel (Leanux.filePpos f) := by
  frame_wg [Leanux.filePpos] using []

theorem filePpos_spec (P : WGKernelView → Prop) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.filePpos f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (filePpos_sameWGKernel f).wp P

theorem filesLookupFdRaw_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.filesLookupFdRaw fd) := by
  frame_wg [Leanux.filesLookupFdRaw] using [fdtSlot_spec]

theorem filesLookupFdRaw_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.filesLookupFdRaw fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (filesLookupFdRaw_sameWGKernel fd).wp P

theorem fopWriteIter_sameWGKernel (iocb : Kiocb) («from» : IovIter) (which : Option FopsId) : SameWGKernel (Leanux.fopWriteIter iocb «from» which) := by
  cases which with
  | none => frame_wg [Leanux.fopWriteIter] using [pipeWrite_spec]
  | some k => cases k <;> frame_wg [Leanux.fopWriteIter] using [pipeWrite_spec]

theorem fopWriteIter_spec (P : WGKernelView → Prop) (iocb : Kiocb) («from» : IovIter) (which : Option FopsId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fopWriteIter iocb «from» which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fopWriteIter_sameWGKernel iocb «from» which).wp P

theorem fopsOf_sameWGKernel  (which : Option FopsId) : SameWGKernel (Leanux.fopsOf which) := by
  cases which with
  | none => frame_wg [Leanux.fopsOf] using []
  | some k => cases k <;> frame_wg [Leanux.fopsOf] using []

theorem fopsOf_spec (P : WGKernelView → Prop)  (which : Option FopsId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fopsOf which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fopsOf_sameWGKernel which).wp P

theorem fullWord_sameWGKernel (fdt : Fdtable) (word : Nat) : SameWGKernel (Leanux.fullWord fdt word) := by
  unfold Leanux.fullWord
  exact allM_sameWGKernel _ _ (fun _ => fdtOpen_sameWGKernel _ _)

theorem fullWord_spec (P : WGKernelView → Prop) (fdt : Fdtable) (word : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fullWord fdt word
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fullWord_sameWGKernel fdt word).wp P

theorem getCloseOnExec_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.getCloseOnExec fd) := by
  frame_wg [Leanux.getCloseOnExec] using [fdtCloexec_spec]

theorem getCloseOnExec_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getCloseOnExec fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getCloseOnExec_sameWGKernel fd).wp P

theorem refcountInc_spec (P : WGKernelView → Prop) (x : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.refcountInc x
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (sameWGKernel_of_sameKernel (Framing.refcountInc_sameKernel x)).wp P

theorem refcountDecAndTest_spec (P : WGKernelView → Prop) (x : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.refcountDecAndTest x
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (sameWGKernel_of_sameKernel (Framing.refcountDecAndTest_sameKernel x)).wp P

theorem refcountIncGuestWide_spec (P : WGKernelView → Prop) (x : OperandExclusion) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.refcountIncGuestWide x
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (sameWGKernel_of_sameKernel (Framing.refcountIncGuestWide_sameKernel x)).wp P

theorem getCurrentUser_sameWGKernel  : SameWGKernel (Leanux.getCurrentUser ) := by
  frame_wg [Leanux.getCurrentUser] using [refcountIncGuestWide_spec]

theorem getCurrentUser_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getCurrentUser
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getCurrentUser_sameWGKernel ).wp P

theorem getFileRef_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.getFileRef fid) := by
  frame_wg [Leanux.getFileRef] using [getFile_spec, setFile_spec]

theorem getFileRef_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getFileRef fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getFileRef_sameWGKernel fid).wp P

theorem getPipeInfo_sameWGKernel (f : File) : SameWGKernel (Leanux.getPipeInfo f) := by
  frame_wg [Leanux.getPipeInfo] using []

theorem getPipeInfo_spec (P : WGKernelView → Prop) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getPipeInfo f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getPipeInfo_sameWGKernel f).wp P

theorem idaAlloc_sameWGKernel  : SameWGKernel (Leanux.idaAlloc ) := by
  frame_wg [Leanux.idaAlloc] using []

theorem idaAlloc_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.idaAlloc
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (idaAlloc_sameWGKernel ).wp P

theorem inodeFileType_sameWGKernel  (which : Option InodeId) : SameWGKernel (Leanux.inodeFileType which) := by
  cases which with
  | none => frame_wg [Leanux.inodeFileType] using [getInode_spec]
  | some k => cases k <;> frame_wg [Leanux.inodeFileType] using [getInode_spec]

theorem inodeFileType_spec (P : WGKernelView → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.inodeFileType which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeFileType_sameWGKernel which).wp P

theorem inodeFlags_sameWGKernel  (which : Option InodeId) : SameWGKernel (Leanux.inodeFlags which) := by
  cases which with
  | none => frame_wg [Leanux.inodeFlags] using [getInode_spec]
  | some k => cases k <;> frame_wg [Leanux.inodeFlags] using [getInode_spec]

theorem inodeFlags_spec (P : WGKernelView → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.inodeFlags which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeFlags_sameWGKernel which).wp P

theorem inodeIsChr_sameWGKernel  (which : Option InodeId) : SameWGKernel (Leanux.inodeIsChr which) := by
  cases which with
  | none => frame_wg [Leanux.inodeIsChr] using [getInode_spec]
  | some k => cases k <;> frame_wg [Leanux.inodeIsChr] using [getInode_spec]

theorem inodeIsChr_spec (P : WGKernelView → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.inodeIsChr which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeIsChr_sameWGKernel which).wp P

theorem inodeIsReg_sameWGKernel  (which : Option InodeId) : SameWGKernel (Leanux.inodeIsReg which) := by
  cases which with
  | none => frame_wg [Leanux.inodeIsReg] using [getInode_spec]
  | some k => cases k <;> frame_wg [Leanux.inodeIsReg] using [getInode_spec]

theorem inodeIsReg_spec (P : WGKernelView → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.inodeIsReg which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeIsReg_sameWGKernel which).wp P

theorem inodeReadcountDec_sameWGKernel  (which : Option InodeId) : SameWGKernel (Leanux.inodeReadcountDec which) := by
  cases which with
  | none => frame_wg [Leanux.inodeReadcountDec] using [getInode_spec, setInode_spec]
  | some k => cases k <;> frame_wg [Leanux.inodeReadcountDec] using [getInode_spec, setInode_spec]

theorem inodeReadcountDec_spec (P : WGKernelView → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.inodeReadcountDec which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeReadcountDec_sameWGKernel which).wp P

theorem inodeReadcountInc_sameWGKernel  (which : Option InodeId) : SameWGKernel (Leanux.inodeReadcountInc which) := by
  cases which with
  | none => frame_wg [Leanux.inodeReadcountInc] using [getInode_spec, setInode_spec]
  | some k => cases k <;> frame_wg [Leanux.inodeReadcountInc] using [getInode_spec, setInode_spec]

theorem inodeReadcountInc_spec (P : WGKernelView → Prop)  (which : Option InodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.inodeReadcountInc which
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeReadcountInc_sameWGKernel which).wp P

theorem iocbFlags_sameWGKernel (fFlags : UInt32) : SameWGKernel (Leanux.iocbFlags fFlags) := by
  frame_wg [Leanux.iocbFlags] using []

theorem iocbFlags_spec (P : WGKernelView → Prop) (fFlags : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.iocbFlags fFlags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (iocbFlags_sameWGKernel fFlags).wp P

theorem iputPipefs_sameWGKernel (id : PipefsInodeId) : SameWGKernel (Leanux.iputPipefs id) := by
  frame_wg [Leanux.iputPipefs] using [getInode_spec, setInode_spec]

theorem iputPipefs_spec (P : WGKernelView → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.iputPipefs id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (iputPipefs_sameWGKernel id).wp P

theorem newInodePseudo_sameWGKernel  : SameWGKernel (Leanux.newInodePseudo ) := by
  frame_wg [Leanux.newInodePseudo] using [envOk_spec, setInode_spec]

theorem newInodePseudo_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.newInodePseudo
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (newInodePseudo_sameWGKernel ).wp P

theorem pipeIsUnprivilegedUser_sameWGKernel  : SameWGKernel (Leanux.pipeIsUnprivilegedUser ) := by
  frame_wg [Leanux.pipeIsUnprivilegedUser] using []

theorem pipeIsUnprivilegedUser_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipeIsUnprivilegedUser
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pipeIsUnprivilegedUser_sameWGKernel ).wp P

theorem pipeUpdateTail_sameWGKernel (pid : PipeId) (i : Nat) (tail : UInt32) : SameWGKernel (Leanux.pipeUpdateTail pid i tail) := by
  frame_wg [Leanux.pipeUpdateTail] using [getPipe_spec, pipeBufRelease_spec, setPipe_spec]

theorem pipeUpdateTail_spec (P : WGKernelView → Prop) (pid : PipeId) (i : Nat) (tail : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipeUpdateTail pid i tail
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pipeUpdateTail_sameWGKernel pid i tail).wp P

theorem roundPipeSize_sameWGKernel (size : Nat) : SameWGKernel (Leanux.roundPipeSize size) := by
  frame_wg [Leanux.roundPipeSize] using []

theorem roundPipeSize_spec (P : WGKernelView → Prop) (size : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.roundPipeSize size
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (roundPipeSize_sameWGKernel size).wp P

theorem rwVerifyArea_sameWGKernel (ppos : Option Int) (count : Nat) : SameWGKernel (Leanux.rwVerifyArea ppos count) := by
  frame_wg [Leanux.rwVerifyArea] using []

theorem rwVerifyArea_spec (P : WGKernelView → Prop) (ppos : Option Int) (count : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.rwVerifyArea ppos count
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (rwVerifyArea_sameWGKernel ppos count).wp P

theorem setCloseOnExecBit_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.setCloseOnExecBit fd) := by
  frame_wg [Leanux.setCloseOnExecBit] using [setFdtCloexec_spec]

theorem setCloseOnExecBit_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setCloseOnExecBit fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setCloseOnExecBit_sameWGKernel fd).wp P

theorem simpleInodeInitTs_sameWGKernel (id : PipefsInodeId) : SameWGKernel (Leanux.simpleInodeInitTs id) := by
  frame_wg [Leanux.simpleInodeInitTs] using [getInode_spec, inodeSetCtimeCurrent_spec, setInode_spec]

theorem simpleInodeInitTs_spec (P : WGKernelView → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.simpleInodeInitTs id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (simpleInodeInitTs_sameWGKernel id).wp P

theorem streamOpen_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.streamOpen fid) := by
  frame_wg [Leanux.streamOpen] using [getFile_spec, setFile_spec]

theorem streamOpen_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.streamOpen fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (streamOpen_sameWGKernel fid).wp P

theorem tooManyPipeBuffersHard_sameWGKernel (userBufs : Nat) : SameWGKernel (Leanux.tooManyPipeBuffersHard userBufs) := by
  frame_wg [Leanux.tooManyPipeBuffersHard] using []

theorem tooManyPipeBuffersHard_spec (P : WGKernelView → Prop) (userBufs : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.tooManyPipeBuffersHard userBufs
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (tooManyPipeBuffersHard_sameWGKernel userBufs).wp P

theorem tooManyPipeBuffersSoft_sameWGKernel (userBufs : Nat) : SameWGKernel (Leanux.tooManyPipeBuffersSoft userBufs) := by
  frame_wg [Leanux.tooManyPipeBuffersSoft] using []

theorem tooManyPipeBuffersSoft_spec (P : WGKernelView → Prop) (userBufs : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.tooManyPipeBuffersSoft userBufs
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (tooManyPipeBuffersSoft_sameWGKernel userBufs).wp P

theorem pipefsInodeOf_sameWGKernel (f : File) (what : String) : SameWGKernel ((pinned_const _private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf) f what) := by
  frame_wg [_private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf] using []

theorem pipefsInodeOf_spec (P : WGKernelView → Prop) (f : File) (what : String) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ (pinned_const _private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf) f what
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pipefsInodeOf_sameWGKernel f what).wp P

theorem allocPipeInfo_sameWGKernel  : SameWGKernel (Leanux.allocPipeInfo ) := by
  frame_wg [Leanux.allocPipeInfo] using [accountPipeBuffers_spec, getCurrentUser_spec, hiddenAlloc_spec, pipeIsUnprivilegedUser_spec, setPipe_spec, tooManyPipeBuffersHard_spec, tooManyPipeBuffersSoft_spec]

theorem allocPipeInfo_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.allocPipeInfo
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (allocPipeInfo_sameWGKernel ).wp P

theorem dputPipefs_sameWGKernel (id : PipefsInodeId) : SameWGKernel (Leanux.dputPipefs id) := by
  frame_wg [Leanux.dputPipefs] using [getInode_spec, iputPipefs_spec, setInode_spec]

theorem dputPipefs_spec (P : WGKernelView → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.dputPipefs id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (dputPipefs_sameWGKernel id).wp P

theorem eventfdCtxPut_sameWGKernel (id : CtxId) : SameWGKernel (Leanux.eventfdCtxPut id) := by
  frame_wg [Leanux.eventfdCtxPut] using [eventfdFreeCtx_spec, getCtx_spec, refcountDecAndTest_spec, setCtx_spec]

theorem eventfdCtxPut_spec (P : WGKernelView → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.eventfdCtxPut id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (eventfdCtxPut_sameWGKernel id).wp P

theorem eventfdRead_sameWGKernel (iocb : Kiocb) (iterCount : Nat) : SameWGKernel (Leanux.eventfdRead iocb iterCount) := by
  frame_wg [Leanux.eventfdRead] using [eventfdCtxDoRead_spec, eventfdCtxOf_spec, getCtx_spec, getFile_spec,
    waitqueueActive_spec, wakeUpLockedPoll_spec]

theorem eventfdRead_spec (P : WGKernelView → Prop) (iocb : Kiocb) (iterCount : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.eventfdRead iocb iterCount
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (eventfdRead_sameWGKernel iocb iterCount).wp P

theorem eventfdWrite_sameWGKernel (fid : FileId) (buf : ByteArray) (count : Nat) : SameWGKernel (Leanux.eventfdWrite fid buf count) := by
  unfold Leanux.eventfdWrite
  repeat' first
    | (view_head Leanux.eventfdCtxOf; with_reducible exact @eventfdCtxOf_sameWGKernel _)
    | (view_head Leanux.getCtx; with_reducible exact @getCtx_sameWGKernel _)
    | (view_head Leanux.getFile; with_reducible exact @getFile_sameWGKernel _)
    | (view_head Leanux.setCtx; with_reducible exact @setCtx_sameWGKernel _ _)
    | (view_head Leanux.wakeUpLockedPoll; with_reducible exact @wakeUpLockedPoll_sameWGKernel _ _)
    | (view_head Leanux.waitqueueActive; with_reducible exact @waitqueueActive_sameWGKernel _)
    | (view_head Leanux.getK; with_reducible exact @getK_sameWGKernel)
    | (view_head Leanux.branch; with_reducible exact @branch_sameWGKernel _ _)
    | (view_head Leanux.branchCmp; with_reducible exact @branchCmp_sameWGKernel _ _ _ _)
    | (view_head Leanux.invariant; with_reducible exact @invariant_sameWGKernel _ _)
    | (view_head Leanux.unsupported; with_reducible exact @unsupported_sameWGKernel _ _)
    | (view_head Leanux.modifyK; intro w x v hr; cases hr; rfl)
    | view_step

theorem eventfdWrite_spec (P : WGKernelView → Prop) (fid : FileId) (buf : ByteArray) (count : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.eventfdWrite fid buf count
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (eventfdWrite_sameWGKernel fid buf count).wp P

theorem expandFdtable_sameWGKernel (nr : Nat) : SameWGKernel (Leanux.expandFdtable nr) := by
  frame_wg [Leanux.expandFdtable] using [allocFdtable_spec, copyFdtable_spec]

theorem expandFdtable_spec (P : WGKernelView → Prop) (nr : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.expandFdtable nr
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (expandFdtable_sameWGKernel nr).wp P

theorem fgetLight_sameWGKernel (fd : Nat) (mask : UInt32) : SameWGKernel (Leanux.fgetLight fd mask) := by
  frame_wg [Leanux.fgetLight] using [filesLookupFdRaw_spec, getFile_spec]

theorem fgetLight_spec (P : WGKernelView → Prop) (fd : Nat) (mask : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fgetLight fd mask
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fgetLight_sameWGKernel fd mask).wp P

theorem fileEndWrite_sameWGKernel (f : File) : SameWGKernel (Leanux.fileEndWrite f) := by
  frame_wg [Leanux.fileEndWrite] using [inodeIsReg_spec]

theorem fileEndWrite_spec (P : WGKernelView → Prop) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fileEndWrite f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fileEndWrite_sameWGKernel f).wp P

theorem fileInitPath_sameWGKernel (fid : FileId) (fopId : FopsId) (inode : InodeId) : SameWGKernel (Leanux.fileInitPath fid fopId inode) := by
  frame_wg [Leanux.fileInitPath] using [fopsOf_spec, getFile_spec, inodeReadcountInc_spec, iocbFlags_spec, setFile_spec]

theorem fileInitPath_spec (P : WGKernelView → Prop) (fid : FileId) (fopId : FopsId) (inode : InodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fileInitPath fid fopId inode
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fileInitPath_sameWGKernel fid fopId inode).wp P

theorem fileStartWrite_sameWGKernel (f : File) : SameWGKernel (Leanux.fileStartWrite f) := by
  frame_wg [Leanux.fileStartWrite] using [inodeIsReg_spec]

theorem fileStartWrite_spec (P : WGKernelView → Prop) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fileStartWrite f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fileStartWrite_sameWGKernel f).wp P

theorem filpFlush_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.filpFlush fid) := by
  frame_wg [Leanux.filpFlush] using [fopsOf_spec, getFile_spec]

theorem filpFlush_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.filpFlush fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (filpFlush_sameWGKernel fid).wp P

theorem findNextFd_sameWGKernel (fdt : Fdtable) (start : Nat) : SameWGKernel (Leanux.findNextFd fdt start) := by
  have word_spec (P : WGKernelView → Prop) (fd : Fdtable) (size start : Nat) :=
    (findNextZeroBit_sameWGKernel (fullWord fd) size start
      (fun i => fullWord_sameWGKernel fd i)).wp P
  have fd_spec (P : WGKernelView → Prop) (fd : Fdtable) (size start : Nat) :=
    (findNextZeroBit_sameWGKernel (fdtOpen fd) size start
      (fun i => fdtOpen_sameWGKernel fd i)).wp P
  frame_wg [Leanux.findNextFd] using [word_spec, fd_spec]

theorem findNextFd_spec (P : WGKernelView → Prop) (fdt : Fdtable) (start : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.findNextFd fdt start
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (findNextFd_sameWGKernel fdt start).wp P

theorem fput_sameWGKernel (fid : FileId) : SameWGKernel (Leanux.fput fid) :=
  (Framing.FSFileRefs.fput_sameWGKernel fid)

theorem fput_spec (P : WGKernelView → Prop) (fid : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fput fid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fput_sameWGKernel fid).wp P

theorem newSyncWrite_sameWGKernel (fid : FileId) (buf : ByteArray) (len : Nat) (ppos : Option Int) : SameWGKernel (Leanux.newSyncWrite fid buf len ppos) := by
  frame_wg [Leanux.newSyncWrite] using [fopWriteIter_spec, getFile_spec]

theorem newSyncWrite_spec (P : WGKernelView → Prop) (fid : FileId) (buf : ByteArray) (len : Nat) (ppos : Option Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.newSyncWrite fid buf len ppos
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (newSyncWrite_sameWGKernel fid buf len ppos).wp P

theorem pipeResizeRing_sameWGKernel (pid : PipeId) (nrSlots : Nat) : SameWGKernel (Leanux.pipeResizeRing pid nrSlots) := by
  frame_wg [Leanux.pipeResizeRing] using [copyPipeBufs_spec, envOk_spec, getPipe_spec, setPipe_spec,
    wakeUpInterruptible_spec]

theorem pipeResizeRing_spec (P : WGKernelView → Prop) (pid : PipeId) (nrSlots : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.pipeResizeRing pid nrSlots
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pipeResizeRing_sameWGKernel pid nrSlots).wp P

theorem putFileAccess_sameWGKernel (f : File) : SameWGKernel (Leanux.putFileAccess f) := by
  frame_wg [Leanux.putFileAccess] using [inodeReadcountDec_spec]

theorem putFileAccess_spec (P : WGKernelView → Prop) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.putFileAccess f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (putFileAccess_sameWGKernel f).wp P

theorem putUnusedFdLocked_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.putUnusedFdLocked fd) := by
  frame_wg [Leanux.putUnusedFdLocked] using [clearOpenFd_spec]

theorem putUnusedFdLocked_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.putUnusedFdLocked fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (putUnusedFdLocked_sameWGKernel fd).wp P

theorem setCloseOnExec_sameWGKernel (fd : Nat) (flag : Bool) : SameWGKernel (Leanux.setCloseOnExec fd flag) := by
  frame_wg [Leanux.setCloseOnExec] using [clearCloseOnExecBit_spec, setCloseOnExecBit_spec]

theorem setCloseOnExec_spec (P : WGKernelView → Prop) (fd : Nat) (flag : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setCloseOnExec fd flag
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setCloseOnExec_sameWGKernel fd flag).wp P

theorem setOpenFd_sameWGKernel (fd : Nat) : SameWGKernel (Leanux.setOpenFd fd) := by
  frame_wg [Leanux.setOpenFd] using [fullWord_spec, setFdtOpen_spec]

theorem setOpenFd_spec (P : WGKernelView → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setOpenFd fd
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setOpenFd_sameWGKernel fd).wp P

theorem setfl_sameWGKernel (fid : FileId) (arg : UInt32) : SameWGKernel (Leanux.setfl fid arg) := by
  frame_wg [Leanux.setfl] using [fopsOf_spec, getFile_spec, inodeFileType_spec, inodeFlags_spec, iocbFlags_spec, setFile_spec]

theorem setfl_spec (P : WGKernelView → Prop) (fid : FileId) (arg : UInt32) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setfl fid arg
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setfl_sameWGKernel fid arg).wp P

end Leanux.Proofs.Framing.FSFrames
