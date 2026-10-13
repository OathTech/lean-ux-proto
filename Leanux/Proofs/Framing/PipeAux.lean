import Leanux.Proofs.Framing.Signal
import Leanux.FS.Pipe

/-! Shared full WireGuard frames for the original inode helpers. -/
namespace Leanux.Proofs.Framing.PipeAux
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing.KernelFrames
set_option maxHeartbeats 800000
set_option pp.structureInstances false

theorem timestampTruncate_sameWGKernel (t : Timespec64) : SameWGKernel (timestampTruncate t) := by
  frame_wg [timestampTruncate] using []

theorem timestampTruncate_spec (P : WGKernelView → Prop) (t : Timespec64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ timestampTruncate t
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (timestampTruncate_sameWGKernel t).wp P

theorem currentTime_sameWGKernel  : SameWGKernel (currentTime ) := by
  frame_wg [currentTime] using [hiddenTimespec_spec, timestampTruncate_spec]

theorem currentTime_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ currentTime
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (currentTime_sameWGKernel ).wp P

theorem timespec64Equal_sameWGKernel (a b : Timespec64) : SameWGKernel (timespec64Equal a b) := by
  frame_wg [timespec64Equal] using []

theorem timespec64Equal_spec (P : WGKernelView → Prop) (a b : Timespec64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ timespec64Equal a b
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (timespec64Equal_sameWGKernel a b).wp P

theorem inodeSetCtimeCurrent_sameWGKernel (id : PipefsInodeId) : SameWGKernel (inodeSetCtimeCurrent id) := by
  frame_wg [inodeSetCtimeCurrent] using [currentTime_spec, getInode_spec, setInode_spec]

theorem inodeSetCtimeCurrent_spec (P : WGKernelView → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ inodeSetCtimeCurrent id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeSetCtimeCurrent_sameWGKernel id).wp P

theorem markInodeDirty_sameWGKernel (id : PipefsInodeId) (flags : Nat) : SameWGKernel (markInodeDirty id flags) := by
  frame_wg [markInodeDirty] using [getInode_spec]

theorem markInodeDirty_spec (P : WGKernelView → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ markInodeDirty id flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (markInodeDirty_sameWGKernel id flags).wp P

theorem inodeUpdateTimestamps_sameWGKernel (id : PipefsInodeId) (flags : Nat) : SameWGKernel (inodeUpdateTimestamps id flags) := by
  frame_wg [inodeUpdateTimestamps] using [currentTime_spec, inodeSetCtimeCurrent_spec, timespec64Equal_spec, getInode_spec, setInode_spec]

theorem inodeUpdateTimestamps_spec (P : WGKernelView → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ inodeUpdateTimestamps id flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeUpdateTimestamps_sameWGKernel id flags).wp P

theorem genericUpdateTime_sameWGKernel (id : PipefsInodeId) (flags : Nat) : SameWGKernel (genericUpdateTime id flags) := by
  frame_wg [genericUpdateTime] using [inodeUpdateTimestamps_spec, markInodeDirty_spec]

theorem genericUpdateTime_spec (P : WGKernelView → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ genericUpdateTime id flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (genericUpdateTime_sameWGKernel id flags).wp P

theorem inodeUpdateTime_sameWGKernel (id : PipefsInodeId) (flags : Nat) : SameWGKernel (inodeUpdateTime id flags) := by
  frame_wg [inodeUpdateTime] using [genericUpdateTime_spec]

theorem inodeUpdateTime_spec (P : WGKernelView → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ inodeUpdateTime id flags
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeUpdateTime_sameWGKernel id flags).wp P

theorem relatimeNeedUpdate_sameWGKernel (now : Timespec64) : SameWGKernel (relatimeNeedUpdate now) := by
  frame_wg [relatimeNeedUpdate] using []

theorem relatimeNeedUpdate_spec (P : WGKernelView → Prop) (now : Timespec64) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ relatimeNeedUpdate now
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (relatimeNeedUpdate_sameWGKernel now).wp P

theorem atimeNeedsUpdate_sameWGKernel (id : PipefsInodeId) : SameWGKernel (atimeNeedsUpdate id) := by
  frame_wg [atimeNeedsUpdate] using [getInode_spec, currentTime_spec, relatimeNeedUpdate_spec, timespec64Equal_spec]

theorem atimeNeedsUpdate_spec (P : WGKernelView → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ atimeNeedsUpdate id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (atimeNeedsUpdate_sameWGKernel id).wp P

theorem touchAtime_sameWGKernel (id : PipefsInodeId) : SameWGKernel (touchAtime id) := by
  frame_wg [touchAtime] using [atimeNeedsUpdate_spec, inodeUpdateTime_spec]

theorem touchAtime_spec (P : WGKernelView → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ touchAtime id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (touchAtime_sameWGKernel id).wp P

theorem fileAccessed_sameWGKernel (f : File) : SameWGKernel (fileAccessed f) := by
  frame_wg [fileAccessed, _private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf] using [touchAtime_spec]

theorem fileAccessed_spec (P : WGKernelView → Prop) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ fileAccessed f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fileAccessed_sameWGKernel f).wp P

theorem inodeNeedsUpdateTime_sameWGKernel (id : PipefsInodeId) : SameWGKernel (inodeNeedsUpdateTime id) := by
  frame_wg [inodeNeedsUpdateTime] using [currentTime_spec, getInode_spec, timespec64Equal_spec]

theorem inodeNeedsUpdateTime_spec (P : WGKernelView → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ inodeNeedsUpdateTime id
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (inodeNeedsUpdateTime_sameWGKernel id).wp P

theorem fileUpdateTime_sameWGKernel (f : File) : SameWGKernel (fileUpdateTime f) := by
  frame_wg [fileUpdateTime, _private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf] using [inodeNeedsUpdateTime_spec, inodeUpdateTime_spec]

theorem fileUpdateTime_spec (P : WGKernelView → Prop) (f : File) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ fileUpdateTime f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (fileUpdateTime_sameWGKernel f).wp P

end Leanux.Proofs.Framing.PipeAux
