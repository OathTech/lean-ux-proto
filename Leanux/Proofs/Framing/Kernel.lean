import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.KernelEffects
import Leanux.Proofs.Framing.FSFileRefs

/-! Full WireGuard kernel framing for the original kernel helpers. Each proof unfolds
only its own body and state primitives; callee contracts keep the projection. -/
namespace Leanux.Proofs.Framing.KernelFrames
open Leanux Leanux.WG Std.Do

theorem hidden_spec (P : WGKernelView → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ hidden site
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (sameWGKernel_of_sameKernel (hidden_sameKernel site)).wp P

theorem skipAmbient_spec (P : WGKernelView → Prop) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ skipAmbient
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ :=
  (sameWGKernel_of_sameKernel skipAmbient_sameKernel).wp P

theorem routeLookup_sameWGKernel (family saddr daddr : Nat) : SameWGKernel (Leanux.routeLookup family saddr daddr) := by
  frame_wg [routeLookup] using []

theorem routeLookup_spec (P : WGKernelView → Prop) (family saddr daddr : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.routeLookup family saddr daddr
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (routeLookup_sameWGKernel family saddr daddr).wp P

theorem unsupported_sameWGKernel {α : Type} (what : String) : SameWGKernel (Leanux.unsupported (α := α) what) := by
  frame_wg [unsupported] using []

theorem unsupported_spec (P : WGKernelView → Prop) {α : Type} (what : String) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.unsupported (α := α) what
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (unsupported_sameWGKernel (α := α) what).wp P

theorem invariant_sameWGKernel {α : Type} (what : String) : SameWGKernel (Leanux.invariant (α := α) what) := by
  frame_wg [invariant] using []

theorem invariant_spec (P : WGKernelView → Prop) {α : Type} (what : String) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.invariant (α := α) what
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (invariant_sameWGKernel (α := α) what).wp P

theorem getK_sameWGKernel  : SameWGKernel (Leanux.getK) := by
  frame_wg [getK] using []

theorem getK_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getK
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getK_sameWGKernel).wp P

theorem getFiles_sameWGKernel  : SameWGKernel (Leanux.getFiles) := by
  frame_wg [getFiles] using []

theorem getFiles_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getFiles
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getFiles_sameWGKernel).wp P

theorem modifyFiles_sameWGKernel (f : FilesStruct → FilesStruct) : SameWGKernel (Leanux.modifyFiles f) := by
  frame_wg [modifyFiles] using []

theorem modifyFiles_spec (P : WGKernelView → Prop) (f : FilesStruct → FilesStruct) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.modifyFiles f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (modifyFiles_sameWGKernel f).wp P

theorem modifyFdt_sameWGKernel (f : Fdtable → Fdtable) : SameWGKernel (Leanux.modifyFdt f) := by
  frame_wg [modifyFdt] using []

theorem modifyFdt_spec (P : WGKernelView → Prop) (f : Fdtable → Fdtable) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.modifyFdt f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (modifyFdt_sameWGKernel f).wp P

theorem branch_sameWGKernel (d : Decision) (outcome : Bool) : SameWGKernel (Leanux.branch d outcome) := by
  frame_wg [branch] using []

theorem branch_spec (P : WGKernelView → Prop) (d : Decision) (outcome : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.branch d outcome
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (branch_sameWGKernel d outcome).wp P

theorem branchCmp_sameWGKernel (d : Decision) (outcome : Bool) (a b : Int) : SameWGKernel (Leanux.branchCmp d outcome a b) := by
  frame_wg [branchCmp] using []

theorem branchCmp_spec (P : WGKernelView → Prop) (d : Decision) (outcome : Bool) (a b : Int) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.branchCmp d outcome a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (branchCmp_sameWGKernel d outcome a b).wp P

theorem branchCmpExcluded_sameWGKernel (d : Decision) (outcome : Bool) (x : OperandExclusion) : SameWGKernel (Leanux.branchCmpExcluded d outcome x) := by
  frame_wg [branchCmpExcluded] using []

theorem branchCmpExcluded_spec (P : WGKernelView → Prop) (d : Decision) (outcome : Bool) (x : OperandExclusion) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.branchCmpExcluded d outcome x
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (branchCmpExcluded_sameWGKernel d outcome x).wp P

theorem envOk_sameWGKernel (site : EnvSite) : SameWGKernel (Leanux.envOk site) := by
  frame_wg [envOk] using []

theorem envOk_spec (P : WGKernelView → Prop) (site : EnvSite) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.envOk site
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (envOk_sameWGKernel site).wp P

theorem hiddenU64_sameWGKernel (s : HiddenSite) : SameWGKernel (Leanux.hiddenU64 s) := by
  frame_wg [hiddenU64] using [hidden_spec]

theorem hiddenU64_spec (P : WGKernelView → Prop) (s : HiddenSite) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.hiddenU64 s
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (hiddenU64_sameWGKernel s).wp P

theorem peekHiddenSite_sameWGKernel  : SameWGKernel (Leanux.peekHiddenSite) := by
  frame_wg [peekHiddenSite] using [skipAmbient_spec]

theorem peekHiddenSite_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.peekHiddenSite
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (peekHiddenSite_sameWGKernel).wp P

theorem peekUnit_sameWGKernel (w : Worker) : SameWGKernel (Leanux.peekUnit w) := by
  frame_wg [peekUnit] using [skipAmbient_spec]

theorem peekUnit_spec (P : WGKernelView → Prop) (w : Worker) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.peekUnit w
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (peekUnit_sameWGKernel w).wp P

theorem recordQueued_sameWGKernel (w : Worker) (pid : Nat) : SameWGKernel (Leanux.recordQueued w pid) := by
  frame_wg [recordQueued] using [hidden_spec]

theorem recordQueued_spec (P : WGKernelView → Prop) (w : Worker) (pid : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.recordQueued w pid
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (recordQueued_sameWGKernel w pid).wp P

theorem queueDeviceWork_sameWGKernel (w : Worker) : SameWGKernel (Leanux.queueDeviceWork w) := by
  frame_wg [queueDeviceWork] using [recordQueued_spec]

theorem queueDeviceWork_spec (P : WGKernelView → Prop) (w : Worker) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.queueDeviceWork w
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (queueDeviceWork_sameWGKernel w).wp P

theorem resolveUnit_sameWGKernel (w : Worker) (unit : Nat) (queue : List Nat) : SameWGKernel (Leanux.resolveUnit w unit queue) := by
  frame_wg [resolveUnit] using []

theorem resolveUnit_spec (P : WGKernelView → Prop) (w : Worker) (unit : Nat) (queue : List Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.resolveUnit w unit queue
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (resolveUnit_sameWGKernel w unit queue).wp P

theorem hiddenClock_sameWGKernel (s : HiddenSite) : SameWGKernel (Leanux.hiddenClock s) :=
  sameWGKernel_of_sameKernel (Framing.hiddenClock_sameKernel s)

theorem hiddenClock_spec (P : WGKernelView → Prop) (s : HiddenSite) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.hiddenClock s
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (hiddenClock_sameWGKernel s).wp P

theorem hiddenTimespec_sameWGKernel (s : HiddenSite) : SameWGKernel (Leanux.hiddenTimespec s) := by
  frame_wg [hiddenTimespec] using [hidden_spec]

theorem hiddenTimespec_spec (P : WGKernelView → Prop) (s : HiddenSite) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.hiddenTimespec s
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (hiddenTimespec_sameWGKernel s).wp P

theorem skipCutSites_sameWGKernel (sites : List HiddenSite) : SameWGKernel (Leanux.skipCutSites sites) := by
  frame_wg [skipCutSites] using [skipAmbient_spec]

theorem skipCutSites_spec (P : WGKernelView → Prop) (sites : List HiddenSite) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.skipCutSites sites
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (skipCutSites_sameWGKernel sites).wp P

theorem skipCut_sameWGKernel (sites : List HiddenSite) : SameWGKernel (Leanux.skipCut sites) := by
  intro w x w' h
  change ((Leanux.skipCutSites sites).run w >>= fun r =>
    pure ((), r.2)) = Except.ok (x, w') at h
  cases hr : (Leanux.skipCutSites sites).run w with
  | error e => simp [hr] at h
  | ok result =>
    rcases result with ⟨v, t⟩
    have hh := skipCutSites_sameWGKernel sites w v t hr
    simp [hr] at h
    rcases h with ⟨rfl, rfl⟩
    exact hh

theorem skipCut_spec (P : WGKernelView → Prop) (sites : List HiddenSite) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.skipCut sites
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (skipCut_sameWGKernel sites).wp P

theorem skipCutExactly_sameWGKernel (site : HiddenSite) (n : Nat) (between : List HiddenSite := []) : SameWGKernel (Leanux.skipCutExactly site n between) := by
  frame_wg [skipCutExactly] using [skipAmbient_spec, skipCut_spec]

theorem skipCutExactly_spec (P : WGKernelView → Prop) (site : HiddenSite) (n : Nat) (between : List HiddenSite := []) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.skipCutExactly site n between
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (skipCutExactly_sameWGKernel site n between).wp P

theorem dropHiddenRecord_sameWGKernel  : SameWGKernel (Leanux.dropHiddenRecord) := by
  frame_wg [dropHiddenRecord] using [skipAmbient_spec]

theorem dropHiddenRecord_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.dropHiddenRecord
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (dropHiddenRecord_sameWGKernel).wp P

theorem discardFloodRecords_sameWGKernel (stop : Nat) (allowed : List Nat) : SameWGKernel (Leanux.discardFloodRecords stop allowed) := by
  frame_wg [discardFloodRecords] using [dropHiddenRecord_spec, peekHiddenSite_spec]

theorem discardFloodRecords_spec (P : WGKernelView → Prop) (stop : Nat) (allowed : List Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.discardFloodRecords stop allowed
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (discardFloodRecords_sameWGKernel stop allowed).wp P

theorem getFile_sameWGKernel (id : FileId) : SameWGKernel (Leanux.getFile id) :=
  FSFileRefs.getFile_sameWGKernel id

theorem getFile_spec (P : WGKernelView → Prop) (id : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getFile id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getFile_sameWGKernel id).wp P

theorem setFile_sameWGKernel (id : FileId) (f : File) : SameWGKernel (Leanux.setFile id f) :=
  FSFileRefs.setFile_sameWGKernel id f

theorem setFile_spec (P : WGKernelView → Prop) (id : FileId) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setFile id f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setFile_sameWGKernel id f).wp P

theorem freeFile_sameWGKernel (id : FileId) : SameWGKernel (Leanux.freeFile id) :=
  FSFileRefs.freeFile_sameWGKernel id

theorem freeFile_spec (P : WGKernelView → Prop) (id : FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.freeFile id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (freeFile_sameWGKernel id).wp P

theorem getCtx_sameWGKernel (id : CtxId) : SameWGKernel (Leanux.getCtx id) := by
  frame_wg [getCtx] using []

theorem getCtx_spec (P : WGKernelView → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getCtx id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getCtx_sameWGKernel id).wp P

theorem setCtx_sameWGKernel (id : CtxId) (c : EventfdCtx) : SameWGKernel (Leanux.setCtx id c) := by
  frame_wg [setCtx] using []

theorem setCtx_spec (P : WGKernelView → Prop) (id : CtxId) (c : EventfdCtx) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setCtx id c
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setCtx_sameWGKernel id c).wp P

theorem freeCtx_sameWGKernel (id : CtxId) : SameWGKernel (Leanux.freeCtx id) := by
  frame_wg [freeCtx] using []

theorem freeCtx_spec (P : WGKernelView → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.freeCtx id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (freeCtx_sameWGKernel id).wp P

theorem getInode_sameWGKernel (id : PipefsInodeId) : SameWGKernel (Leanux.getInode id) := by
  frame_wg [getInode] using []

theorem getInode_spec (P : WGKernelView → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getInode id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getInode_sameWGKernel id).wp P

theorem setInode_sameWGKernel (id : PipefsInodeId) (i : Inode) : SameWGKernel (Leanux.setInode id i) := by
  frame_wg [setInode] using []

theorem setInode_spec (P : WGKernelView → Prop) (id : PipefsInodeId) (i : Inode) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setInode id i
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setInode_sameWGKernel id i).wp P

theorem getPipe_sameWGKernel (id : PipeId) : SameWGKernel (Leanux.getPipe id) := by
  frame_wg [getPipe] using []

theorem getPipe_spec (P : WGKernelView → Prop) (id : PipeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getPipe id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getPipe_sameWGKernel id).wp P

theorem setPipe_sameWGKernel (id : PipeId) (p : PipeInodeInfo) : SameWGKernel (Leanux.setPipe id p) := by
  frame_wg [setPipe] using []

theorem setPipe_spec (P : WGKernelView → Prop) (id : PipeId) (p : PipeInodeInfo) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setPipe id p
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setPipe_sameWGKernel id p).wp P

theorem getPage_sameWGKernel (id : PageId) : SameWGKernel (Leanux.getPage id) := by
  frame_wg [getPage] using []

theorem getPage_spec (P : WGKernelView → Prop) (id : PageId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.getPage id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getPage_sameWGKernel id).wp P

theorem setPage_sameWGKernel (id : PageId) (p : Page) : SameWGKernel (Leanux.setPage id p) := by
  frame_wg [setPage] using []

theorem setPage_spec (P : WGKernelView → Prop) (id : PageId) (p : Page) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setPage id p
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setPage_sameWGKernel id p).wp P

theorem fdtSlot_sameWGKernel (fdt : Fdtable) (n : Nat) : SameWGKernel (Leanux.fdtSlot fdt n) := by
  frame_wg [fdtSlot, _private.Leanux.Kernel.Defs.«0».Leanux.at?] using []

theorem fdtSlot_spec (P : WGKernelView → Prop) (fdt : Fdtable) (n : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fdtSlot fdt n
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fdtSlot_sameWGKernel fdt n).wp P

theorem fdtOpen_sameWGKernel (fdt : Fdtable) (n : Nat) : SameWGKernel (Leanux.fdtOpen fdt n) := by
  frame_wg [fdtOpen, _private.Leanux.Kernel.Defs.«0».Leanux.at?] using []

theorem fdtOpen_spec (P : WGKernelView → Prop) (fdt : Fdtable) (n : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fdtOpen fdt n
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fdtOpen_sameWGKernel fdt n).wp P

theorem fdtCloexec_sameWGKernel (fdt : Fdtable) (n : Nat) : SameWGKernel (Leanux.fdtCloexec fdt n) := by
  frame_wg [fdtCloexec, _private.Leanux.Kernel.Defs.«0».Leanux.at?] using []

theorem fdtCloexec_spec (P : WGKernelView → Prop) (fdt : Fdtable) (n : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.fdtCloexec fdt n
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fdtCloexec_sameWGKernel fdt n).wp P

theorem setFdtSlot_sameWGKernel (n : Nat) (v : Option FileId) : SameWGKernel (Leanux.setFdtSlot n v) := by
  frame_wg [setFdtSlot, _private.Leanux.Kernel.Defs.«0».Leanux.setAt] using []

theorem setFdtSlot_spec (P : WGKernelView → Prop) (n : Nat) (v : Option FileId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setFdtSlot n v
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setFdtSlot_sameWGKernel n v).wp P

theorem setFdtOpen_sameWGKernel (n : Nat) (b : Bool) : SameWGKernel (Leanux.setFdtOpen n b) := by
  frame_wg [setFdtOpen, _private.Leanux.Kernel.Defs.«0».Leanux.setAt] using []

theorem setFdtOpen_spec (P : WGKernelView → Prop) (n : Nat) (b : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setFdtOpen n b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setFdtOpen_sameWGKernel n b).wp P

theorem setFdtCloexec_sameWGKernel (n : Nat) (b : Bool) : SameWGKernel (Leanux.setFdtCloexec n b) := by
  frame_wg [setFdtCloexec, _private.Leanux.Kernel.Defs.«0».Leanux.setAt] using []

theorem setFdtCloexec_spec (P : WGKernelView → Prop) (n : Nat) (b : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ Leanux.setFdtCloexec n b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (setFdtCloexec_sameWGKernel n b).wp P

end Leanux.Proofs.Framing.KernelFrames
