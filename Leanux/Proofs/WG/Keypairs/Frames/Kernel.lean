import Leanux.Proofs.WG.Keypairs.Frames.Tools

/-! Receive-state framing for the original kernel helpers. Each proof unfolds
only its own body and state primitives; callee contracts keep the projection. -/
namespace Leanux.Proofs.WG.Keypairs.KernelFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs

theorem routeLookup_sameSnapshot (family saddr daddr : Nat) : SameSnapshot (Leanux.routeLookup family saddr daddr) := by
  frame_same [routeLookup] using []

theorem routeLookup_spec (P : Snapshot → Prop) (family saddr daddr : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.routeLookup family saddr daddr
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (routeLookup_sameSnapshot family saddr daddr).wp P

theorem unsupported_sameSnapshot {α : Type} (what : String) : SameSnapshot (Leanux.unsupported (α := α) what) := by
  frame_same [unsupported] using []

theorem unsupported_spec (P : Snapshot → Prop) {α : Type} (what : String) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.unsupported (α := α) what
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (unsupported_sameSnapshot (α := α) what).wp P

theorem invariant_sameSnapshot {α : Type} (what : String) : SameSnapshot (Leanux.invariant (α := α) what) := by
  frame_same [invariant] using []

theorem invariant_spec (P : Snapshot → Prop) {α : Type} (what : String) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.invariant (α := α) what
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (invariant_sameSnapshot (α := α) what).wp P

theorem getK_sameSnapshot  : SameSnapshot (Leanux.getK) := by
  frame_same [getK] using []

theorem getK_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getK
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getK_sameSnapshot).wp P

theorem getFiles_sameSnapshot  : SameSnapshot (Leanux.getFiles) := by
  frame_same [getFiles] using []

theorem getFiles_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getFiles
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getFiles_sameSnapshot).wp P

theorem modifyFiles_sameSnapshot (f : FilesStruct → FilesStruct) : SameSnapshot (Leanux.modifyFiles f) := by
  frame_same [modifyFiles] using []

theorem modifyFiles_spec (P : Snapshot → Prop) (f : FilesStruct → FilesStruct) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.modifyFiles f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (modifyFiles_sameSnapshot f).wp P

theorem modifyFdt_sameSnapshot (f : Fdtable → Fdtable) : SameSnapshot (Leanux.modifyFdt f) := by
  frame_same [modifyFdt] using []

theorem modifyFdt_spec (P : Snapshot → Prop) (f : Fdtable → Fdtable) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.modifyFdt f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (modifyFdt_sameSnapshot f).wp P

theorem branch_sameSnapshot (d : Decision) (outcome : Bool) : SameSnapshot (Leanux.branch d outcome) := by
  frame_same [branch] using []

theorem branch_spec (P : Snapshot → Prop) (d : Decision) (outcome : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.branch d outcome
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (branch_sameSnapshot d outcome).wp P

theorem branchCmp_sameSnapshot (d : Decision) (outcome : Bool) (a b : Int) : SameSnapshot (Leanux.branchCmp d outcome a b) := by
  frame_same [branchCmp] using []

theorem branchCmp_spec (P : Snapshot → Prop) (d : Decision) (outcome : Bool) (a b : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.branchCmp d outcome a b
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (branchCmp_sameSnapshot d outcome a b).wp P

theorem branchCmpExcluded_sameSnapshot (d : Decision) (outcome : Bool) (x : OperandExclusion) : SameSnapshot (Leanux.branchCmpExcluded d outcome x) := by
  frame_same [branchCmpExcluded] using []

theorem branchCmpExcluded_spec (P : Snapshot → Prop) (d : Decision) (outcome : Bool) (x : OperandExclusion) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.branchCmpExcluded d outcome x
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (branchCmpExcluded_sameSnapshot d outcome x).wp P

theorem envOk_sameSnapshot (site : EnvSite) : SameSnapshot (Leanux.envOk site) := by
  frame_same [envOk] using []

theorem envOk_spec (P : Snapshot → Prop) (site : EnvSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.envOk site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (envOk_sameSnapshot site).wp P

theorem hiddenU64_sameSnapshot (s : HiddenSite) : SameSnapshot (Leanux.hiddenU64 s) := by
  frame_same [hiddenU64] using [hidden_snapshot_spec]

theorem hiddenU64_spec (P : Snapshot → Prop) (s : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.hiddenU64 s
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (hiddenU64_sameSnapshot s).wp P

theorem peekHiddenSite_sameSnapshot  : SameSnapshot (Leanux.peekHiddenSite) := by
  frame_same [peekHiddenSite] using [skipAmbient_snapshot_spec]

theorem peekHiddenSite_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.peekHiddenSite
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peekHiddenSite_sameSnapshot).wp P

theorem peekUnit_sameSnapshot (w : Worker) : SameSnapshot (Leanux.peekUnit w) := by
  frame_same [peekUnit] using [skipAmbient_snapshot_spec]

theorem peekUnit_spec (P : Snapshot → Prop) (w : Worker) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.peekUnit w
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peekUnit_sameSnapshot w).wp P

theorem recordQueued_sameSnapshot (w : Worker) (pid : Nat) : SameSnapshot (Leanux.recordQueued w pid) := by
  frame_same [recordQueued] using [hidden_snapshot_spec]

theorem recordQueued_spec (P : Snapshot → Prop) (w : Worker) (pid : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.recordQueued w pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (recordQueued_sameSnapshot w pid).wp P

theorem queueDeviceWork_sameSnapshot (w : Worker) : SameSnapshot (Leanux.queueDeviceWork w) := by
  frame_same [queueDeviceWork] using [recordQueued_spec]

theorem queueDeviceWork_spec (P : Snapshot → Prop) (w : Worker) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.queueDeviceWork w
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (queueDeviceWork_sameSnapshot w).wp P

theorem resolveUnit_sameSnapshot (w : Worker) (unit : Nat) (queue : List Nat) : SameSnapshot (Leanux.resolveUnit w unit queue) := by
  frame_same [resolveUnit] using []

theorem resolveUnit_spec (P : Snapshot → Prop) (w : Worker) (unit : Nat) (queue : List Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.resolveUnit w unit queue
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (resolveUnit_sameSnapshot w unit queue).wp P

theorem hiddenClock_sameSnapshot (s : HiddenSite) : SameSnapshot (Leanux.hiddenClock s) := by
  frame_same [hiddenClock] using [hidden_snapshot_spec]

theorem hiddenClock_spec (P : Snapshot → Prop) (s : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.hiddenClock s
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (hiddenClock_sameSnapshot s).wp P

theorem hiddenTimespec_sameSnapshot (s : HiddenSite) : SameSnapshot (Leanux.hiddenTimespec s) := by
  frame_same [hiddenTimespec] using [hidden_snapshot_spec]

theorem hiddenTimespec_spec (P : Snapshot → Prop) (s : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.hiddenTimespec s
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (hiddenTimespec_sameSnapshot s).wp P

theorem skipCutSites_sameSnapshot (sites : List HiddenSite) : SameSnapshot (Leanux.skipCutSites sites) := by
  frame_same [skipCutSites] using [skipAmbient_snapshot_spec]

theorem skipCutSites_spec (P : Snapshot → Prop) (sites : List HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.skipCutSites sites
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (skipCutSites_sameSnapshot sites).wp P

theorem skipCut_sameSnapshot (sites : List HiddenSite) : SameSnapshot (Leanux.skipCut sites) := by
  intro w x w' h
  change ((Leanux.skipCutSites sites).run w >>= fun r =>
    pure ((), r.2)) = Except.ok (x, w') at h
  cases hr : (Leanux.skipCutSites sites).run w with
  | error e => simp [hr] at h
  | ok result =>
    rcases result with ⟨v, t⟩
    have hh := skipCutSites_sameSnapshot sites w v t hr
    simp [hr] at h
    rcases h with ⟨rfl, rfl⟩
    exact hh

theorem skipCut_spec (P : Snapshot → Prop) (sites : List HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.skipCut sites
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (skipCut_sameSnapshot sites).wp P

theorem skipCutExactly_sameSnapshot (site : HiddenSite) (n : Nat) (between : List HiddenSite := []) : SameSnapshot (Leanux.skipCutExactly site n between) := by
  frame_same [skipCutExactly] using [skipAmbient_snapshot_spec, skipCut_spec]

theorem skipCutExactly_spec (P : Snapshot → Prop) (site : HiddenSite) (n : Nat) (between : List HiddenSite := []) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.skipCutExactly site n between
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (skipCutExactly_sameSnapshot site n between).wp P

theorem dropHiddenRecord_sameSnapshot  : SameSnapshot (Leanux.dropHiddenRecord) := by
  frame_same [dropHiddenRecord] using [skipAmbient_snapshot_spec]

theorem dropHiddenRecord_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.dropHiddenRecord
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dropHiddenRecord_sameSnapshot).wp P

theorem discardFloodRecords_sameSnapshot (stop : Nat) (allowed : List Nat) : SameSnapshot (Leanux.discardFloodRecords stop allowed) := by
  frame_same [discardFloodRecords] using [dropHiddenRecord_spec, peekHiddenSite_spec]

theorem discardFloodRecords_spec (P : Snapshot → Prop) (stop : Nat) (allowed : List Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.discardFloodRecords stop allowed
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (discardFloodRecords_sameSnapshot stop allowed).wp P

theorem getFile_sameSnapshot (id : FileId) : SameSnapshot (Leanux.getFile id) := by
  frame_same [getFile] using []

theorem getFile_spec (P : Snapshot → Prop) (id : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getFile id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getFile_sameSnapshot id).wp P

theorem setFile_sameSnapshot (id : FileId) (f : File) : SameSnapshot (Leanux.setFile id f) := by
  frame_same [setFile] using []

theorem setFile_spec (P : Snapshot → Prop) (id : FileId) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setFile id f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setFile_sameSnapshot id f).wp P

theorem freeFile_sameSnapshot (id : FileId) : SameSnapshot (Leanux.freeFile id) := by
  frame_same [freeFile] using []

theorem freeFile_spec (P : Snapshot → Prop) (id : FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freeFile id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeFile_sameSnapshot id).wp P

theorem getCtx_sameSnapshot (id : CtxId) : SameSnapshot (Leanux.getCtx id) := by
  frame_same [getCtx] using []

theorem getCtx_spec (P : Snapshot → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getCtx id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getCtx_sameSnapshot id).wp P

theorem setCtx_sameSnapshot (id : CtxId) (c : EventfdCtx) : SameSnapshot (Leanux.setCtx id c) := by
  frame_same [setCtx] using []

theorem setCtx_spec (P : Snapshot → Prop) (id : CtxId) (c : EventfdCtx) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setCtx id c
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setCtx_sameSnapshot id c).wp P

theorem freeCtx_sameSnapshot (id : CtxId) : SameSnapshot (Leanux.freeCtx id) := by
  frame_same [freeCtx] using []

theorem freeCtx_spec (P : Snapshot → Prop) (id : CtxId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.freeCtx id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (freeCtx_sameSnapshot id).wp P

theorem getInode_sameSnapshot (id : PipefsInodeId) : SameSnapshot (Leanux.getInode id) := by
  frame_same [getInode] using []

theorem getInode_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getInode id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getInode_sameSnapshot id).wp P

theorem setInode_sameSnapshot (id : PipefsInodeId) (i : Inode) : SameSnapshot (Leanux.setInode id i) := by
  frame_same [setInode] using []

theorem setInode_spec (P : Snapshot → Prop) (id : PipefsInodeId) (i : Inode) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setInode id i
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setInode_sameSnapshot id i).wp P

theorem getPipe_sameSnapshot (id : PipeId) : SameSnapshot (Leanux.getPipe id) := by
  frame_same [getPipe] using []

theorem getPipe_spec (P : Snapshot → Prop) (id : PipeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getPipe id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getPipe_sameSnapshot id).wp P

theorem setPipe_sameSnapshot (id : PipeId) (p : PipeInodeInfo) : SameSnapshot (Leanux.setPipe id p) := by
  frame_same [setPipe] using []

theorem setPipe_spec (P : Snapshot → Prop) (id : PipeId) (p : PipeInodeInfo) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setPipe id p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPipe_sameSnapshot id p).wp P

theorem getPage_sameSnapshot (id : PageId) : SameSnapshot (Leanux.getPage id) := by
  frame_same [getPage] using []

theorem getPage_spec (P : Snapshot → Prop) (id : PageId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.getPage id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getPage_sameSnapshot id).wp P

theorem setPage_sameSnapshot (id : PageId) (p : Page) : SameSnapshot (Leanux.setPage id p) := by
  frame_same [setPage] using []

theorem setPage_spec (P : Snapshot → Prop) (id : PageId) (p : Page) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setPage id p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPage_sameSnapshot id p).wp P

theorem fdtSlot_sameSnapshot (fdt : Fdtable) (n : Nat) : SameSnapshot (Leanux.fdtSlot fdt n) := by
  frame_same [fdtSlot, _private.Leanux.Kernel.Defs.«0».Leanux.at?] using []

theorem fdtSlot_spec (P : Snapshot → Prop) (fdt : Fdtable) (n : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fdtSlot fdt n
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fdtSlot_sameSnapshot fdt n).wp P

theorem fdtOpen_sameSnapshot (fdt : Fdtable) (n : Nat) : SameSnapshot (Leanux.fdtOpen fdt n) := by
  frame_same [fdtOpen, _private.Leanux.Kernel.Defs.«0».Leanux.at?] using []

theorem fdtOpen_spec (P : Snapshot → Prop) (fdt : Fdtable) (n : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fdtOpen fdt n
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fdtOpen_sameSnapshot fdt n).wp P

theorem fdtCloexec_sameSnapshot (fdt : Fdtable) (n : Nat) : SameSnapshot (Leanux.fdtCloexec fdt n) := by
  frame_same [fdtCloexec, _private.Leanux.Kernel.Defs.«0».Leanux.at?] using []

theorem fdtCloexec_spec (P : Snapshot → Prop) (fdt : Fdtable) (n : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.fdtCloexec fdt n
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fdtCloexec_sameSnapshot fdt n).wp P

theorem setFdtSlot_sameSnapshot (n : Nat) (v : Option FileId) : SameSnapshot (Leanux.setFdtSlot n v) := by
  frame_same [setFdtSlot, _private.Leanux.Kernel.Defs.«0».Leanux.setAt] using []

theorem setFdtSlot_spec (P : Snapshot → Prop) (n : Nat) (v : Option FileId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setFdtSlot n v
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setFdtSlot_sameSnapshot n v).wp P

theorem setFdtOpen_sameSnapshot (n : Nat) (b : Bool) : SameSnapshot (Leanux.setFdtOpen n b) := by
  frame_same [setFdtOpen, _private.Leanux.Kernel.Defs.«0».Leanux.setAt] using []

theorem setFdtOpen_spec (P : Snapshot → Prop) (n : Nat) (b : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setFdtOpen n b
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setFdtOpen_sameSnapshot n b).wp P

theorem setFdtCloexec_sameSnapshot (n : Nat) (b : Bool) : SameSnapshot (Leanux.setFdtCloexec n b) := by
  frame_same [setFdtCloexec, _private.Leanux.Kernel.Defs.«0».Leanux.setAt] using []

theorem setFdtCloexec_spec (P : Snapshot → Prop) (n : Nat) (b : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.setFdtCloexec n b
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setFdtCloexec_sameSnapshot n b).wp P

end Leanux.Proofs.WG.Keypairs.KernelFrames
