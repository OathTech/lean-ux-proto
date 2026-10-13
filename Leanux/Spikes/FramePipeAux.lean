import Leanux.Spikes.FrameKernel
import Leanux.FS.Pipe

/-! Receive-state framing of the original signal and inode helpers reached by
pipe reads and writes. -/
namespace Leanux.Spikes.Lifetimes.PipeAux
open Leanux Leanux.WG Std.Do Leanux.Spikes.Framing
open Leanux.Spikes.Lifetimes Leanux.Spikes.Lifetimes.KernelFrames

set_option pp.structureInstances false
set_option maxHeartbeats 800000

theorem sigqueueAlloc_sameSnapshot (overrideRlimit : Nat) : SameSnapshot (sigqueueAlloc overrideRlimit) := by
  frame_same [sigqueueAlloc] using [envOk_spec]

theorem sigqueueAlloc_spec (P : Snapshot → Prop) (overrideRlimit : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sigqueueAlloc overrideRlimit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sigqueueAlloc_sameSnapshot overrideRlimit).wp P

theorem sigIgnored_sameSnapshot (sig : Nat) : SameSnapshot (sigIgnored sig) := by
  frame_same [sigIgnored] using []

theorem sigIgnored_spec (P : Snapshot → Prop) (sig : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sigIgnored sig
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sigIgnored_sameSnapshot sig).wp P

theorem prepareSignal_sameSnapshot (sig : Nat) : SameSnapshot (prepareSignal sig) := by
  frame_same [prepareSignal] using [sigIgnored_spec]

theorem prepareSignal_spec (P : Snapshot → Prop) (sig : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ prepareSignal sig
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (prepareSignal_sameSnapshot sig).wp P

theorem legacyQueue_sameSnapshot (pending : SigSet) (sig : Nat) : SameSnapshot (legacyQueue pending sig) := by
  frame_same [legacyQueue] using []

theorem legacyQueue_spec (P : Snapshot → Prop) (pending : SigSet) (sig : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ legacyQueue pending sig
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (legacyQueue_sameSnapshot pending sig).wp P

theorem wantsSignal_sameSnapshot (sig : Nat) : SameSnapshot (wantsSignal sig) := by
  frame_same [wantsSignal] using []

theorem wantsSignal_spec (P : Snapshot → Prop) (sig : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wantsSignal sig
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wantsSignal_sameSnapshot sig).wp P

theorem completeSignal_sameSnapshot (sig type : Nat) : SameSnapshot (completeSignal sig type) := by
  frame_same [completeSignal] using [wantsSignal_spec]

theorem completeSignal_spec (P : Snapshot → Prop) (sig type : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ completeSignal sig type
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (completeSignal_sameSnapshot sig type).wp P

theorem sendSignalLocked'_sameSnapshot (sig : Nat) (info : SigInfo) (type : Nat) (force : Bool) : SameSnapshot (sendSignalLocked' sig info type force) := by
  frame_same [sendSignalLocked'] using [prepareSignal_spec, legacyQueue_spec, sigqueueAlloc_spec, completeSignal_spec]

theorem sendSignalLocked'_spec (P : Snapshot → Prop) (sig : Nat) (info : SigInfo) (type : Nat) (force : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sendSignalLocked' sig info type force
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendSignalLocked'_sameSnapshot sig info type force).wp P

theorem sendSignalLocked_sameSnapshot (sig : Nat) (info : SigInfo) (type : Nat) : SameSnapshot (sendSignalLocked sig info type) := by
  frame_same [sendSignalLocked] using [sendSignalLocked'_spec]

theorem sendSignalLocked_spec (P : Snapshot → Prop) (sig : Nat) (info : SigInfo) (type : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sendSignalLocked sig info type
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendSignalLocked_sameSnapshot sig info type).wp P

theorem doSendSigInfo_sameSnapshot (sig : Nat) (info : SigInfo) (type : Nat) : SameSnapshot (doSendSigInfo sig info type) := by
  frame_same [doSendSigInfo] using [sendSignalLocked_spec]

theorem doSendSigInfo_spec (P : Snapshot → Prop) (sig : Nat) (info : SigInfo) (type : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ doSendSigInfo sig info type
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doSendSigInfo_sameSnapshot sig info type).wp P

theorem sendSigInfo_sameSnapshot (sig : Nat) (info : SigInfo) : SameSnapshot (sendSigInfo sig info) := by
  frame_same [sendSigInfo] using [doSendSigInfo_spec]

theorem sendSigInfo_spec (P : Snapshot → Prop) (sig : Nat) (info : SigInfo) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sendSigInfo sig info
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendSigInfo_sameSnapshot sig info).wp P

theorem sendSig_sameSnapshot (sig priv : Nat) : SameSnapshot (sendSig sig priv) := by
  frame_same [sendSig] using [sendSigInfo_spec]

theorem sendSig_spec (P : Snapshot → Prop) (sig priv : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sendSig sig priv
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendSig_sameSnapshot sig priv).wp P

theorem timestampTruncate_sameSnapshot (t : Timespec64) : SameSnapshot (timestampTruncate t) := by
  frame_same [timestampTruncate] using []

theorem timestampTruncate_spec (P : Snapshot → Prop) (t : Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ timestampTruncate t
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timestampTruncate_sameSnapshot t).wp P

theorem currentTime_sameSnapshot  : SameSnapshot (currentTime ) := by
  frame_same [currentTime] using [hiddenTimespec_spec, timestampTruncate_spec]

theorem currentTime_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ currentTime
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (currentTime_sameSnapshot ).wp P

theorem timespec64Equal_sameSnapshot (a b : Timespec64) : SameSnapshot (timespec64Equal a b) := by
  frame_same [timespec64Equal] using []

theorem timespec64Equal_spec (P : Snapshot → Prop) (a b : Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ timespec64Equal a b
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timespec64Equal_sameSnapshot a b).wp P

theorem inodeSetCtimeCurrent_sameSnapshot (id : PipefsInodeId) : SameSnapshot (inodeSetCtimeCurrent id) := by
  frame_same [inodeSetCtimeCurrent] using [currentTime_spec, getInode_spec, setInode_spec]

theorem inodeSetCtimeCurrent_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ inodeSetCtimeCurrent id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeSetCtimeCurrent_sameSnapshot id).wp P

theorem markInodeDirty_sameSnapshot (id : PipefsInodeId) (flags : Nat) : SameSnapshot (markInodeDirty id flags) := by
  frame_same [markInodeDirty] using [getInode_spec]

theorem markInodeDirty_spec (P : Snapshot → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ markInodeDirty id flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (markInodeDirty_sameSnapshot id flags).wp P

theorem inodeUpdateTimestamps_sameSnapshot (id : PipefsInodeId) (flags : Nat) : SameSnapshot (inodeUpdateTimestamps id flags) := by
  frame_same [inodeUpdateTimestamps] using [currentTime_spec, inodeSetCtimeCurrent_spec, timespec64Equal_spec, getInode_spec, setInode_spec]

theorem inodeUpdateTimestamps_spec (P : Snapshot → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ inodeUpdateTimestamps id flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeUpdateTimestamps_sameSnapshot id flags).wp P

theorem genericUpdateTime_sameSnapshot (id : PipefsInodeId) (flags : Nat) : SameSnapshot (genericUpdateTime id flags) := by
  frame_same [genericUpdateTime] using [inodeUpdateTimestamps_spec, markInodeDirty_spec]

theorem genericUpdateTime_spec (P : Snapshot → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ genericUpdateTime id flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (genericUpdateTime_sameSnapshot id flags).wp P

theorem inodeUpdateTime_sameSnapshot (id : PipefsInodeId) (flags : Nat) : SameSnapshot (inodeUpdateTime id flags) := by
  frame_same [inodeUpdateTime] using [genericUpdateTime_spec]

theorem inodeUpdateTime_spec (P : Snapshot → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ inodeUpdateTime id flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeUpdateTime_sameSnapshot id flags).wp P

theorem relatimeNeedUpdate_sameSnapshot (now : Timespec64) : SameSnapshot (relatimeNeedUpdate now) := by
  frame_same [relatimeNeedUpdate] using []

theorem relatimeNeedUpdate_spec (P : Snapshot → Prop) (now : Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ relatimeNeedUpdate now
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (relatimeNeedUpdate_sameSnapshot now).wp P

theorem atimeNeedsUpdate_sameSnapshot (id : PipefsInodeId) : SameSnapshot (atimeNeedsUpdate id) := by
  frame_same [atimeNeedsUpdate] using [getInode_spec, currentTime_spec, relatimeNeedUpdate_spec, timespec64Equal_spec]

theorem atimeNeedsUpdate_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ atimeNeedsUpdate id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (atimeNeedsUpdate_sameSnapshot id).wp P

theorem touchAtime_sameSnapshot (id : PipefsInodeId) : SameSnapshot (touchAtime id) := by
  frame_same [touchAtime] using [atimeNeedsUpdate_spec, inodeUpdateTime_spec]

theorem touchAtime_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ touchAtime id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (touchAtime_sameSnapshot id).wp P

theorem fileAccessed_sameSnapshot (f : File) : SameSnapshot (fileAccessed f) := by
  frame_same [fileAccessed, _private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf] using [touchAtime_spec]

theorem fileAccessed_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ fileAccessed f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileAccessed_sameSnapshot f).wp P

theorem inodeNeedsUpdateTime_sameSnapshot (id : PipefsInodeId) : SameSnapshot (inodeNeedsUpdateTime id) := by
  frame_same [inodeNeedsUpdateTime] using [currentTime_spec, getInode_spec, timespec64Equal_spec]

theorem inodeNeedsUpdateTime_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ inodeNeedsUpdateTime id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeNeedsUpdateTime_sameSnapshot id).wp P

theorem fileUpdateTime_sameSnapshot (f : File) : SameSnapshot (fileUpdateTime f) := by
  frame_same [fileUpdateTime, _private.Leanux.FS.Inode.«0».Leanux.pipefsInodeOf] using [inodeNeedsUpdateTime_spec, inodeUpdateTime_spec]

theorem fileUpdateTime_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ fileUpdateTime f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileUpdateTime_sameSnapshot f).wp P

end Leanux.Spikes.Lifetimes.PipeAux
