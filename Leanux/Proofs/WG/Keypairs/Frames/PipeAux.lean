import Leanux.Proofs.WG.Keypairs.Frames.Kernel
import Leanux.Proofs.Framing.PipeAux

/-! Legacy receive-state projections of the shared signal and inode frames. -/
namespace Leanux.Proofs.WG.Keypairs.PipeAux
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing Leanux.Proofs.WG.Keypairs

theorem sigqueueAlloc_sameSnapshot (overrideRlimit : Nat) : SameSnapshot (sigqueueAlloc overrideRlimit) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.sigqueueAlloc_sameWGKernel overrideRlimit)

theorem sigqueueAlloc_spec (P : Snapshot → Prop) (overrideRlimit : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sigqueueAlloc overrideRlimit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sigqueueAlloc_sameSnapshot overrideRlimit).wp P

theorem sigIgnored_sameSnapshot (t : TaskRef) (sig : Nat) (force : Bool := false) : SameSnapshot (sigIgnored t sig force) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.sigIgnored_sameWGKernel t sig force)

theorem sigIgnored_spec (P : Snapshot → Prop) (t : TaskRef) (sig : Nat) (force : Bool := false) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sigIgnored t sig force
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sigIgnored_sameSnapshot t sig force).wp P

theorem prepareSignal_sameSnapshot (t : TaskRef) (sig : Nat) (force : Bool := false) : SameSnapshot (prepareSignal t sig force) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.prepareSignal_sameWGKernel t sig force)

theorem prepareSignal_spec (P : Snapshot → Prop) (t : TaskRef) (sig : Nat) (force : Bool := false) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ prepareSignal t sig force
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (prepareSignal_sameSnapshot t sig force).wp P

theorem legacyQueue_sameSnapshot (pending : SigSet) (sig : Nat) : SameSnapshot (legacyQueue pending sig) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.legacyQueue_sameWGKernel pending sig)

theorem legacyQueue_spec (P : Snapshot → Prop) (pending : SigSet) (sig : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ legacyQueue pending sig
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (legacyQueue_sameSnapshot pending sig).wp P

theorem wantsSignal_sameSnapshot (t : TaskRef) (sig : Nat) : SameSnapshot (wantsSignal t sig) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.wantsSignal_sameWGKernel t sig)

theorem wantsSignal_spec (P : Snapshot → Prop) (t : TaskRef) (sig : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wantsSignal t sig
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wantsSignal_sameSnapshot t sig).wp P

theorem completeSignal_sameSnapshot (t : TaskRef) (sig type : Nat) : SameSnapshot (completeSignal t sig type) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.completeSignal_sameWGKernel t sig type)

theorem completeSignal_spec (P : Snapshot → Prop) (t : TaskRef) (sig type : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ completeSignal t sig type
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (completeSignal_sameSnapshot t sig type).wp P

theorem sendSignalLocked'_sameSnapshot (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) (force : Bool) : SameSnapshot (sendSignalLocked' t sig info type force) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.sendSignalLocked'_sameWGKernel t sig info type force)

theorem sendSignalLocked'_spec (P : Snapshot → Prop) (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) (force : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sendSignalLocked' t sig info type force
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendSignalLocked'_sameSnapshot t sig info type force).wp P

theorem sendSignalLocked_sameSnapshot (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) : SameSnapshot (sendSignalLocked t sig info type) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.sendSignalLocked_sameWGKernel t sig info type)

theorem sendSignalLocked_spec (P : Snapshot → Prop) (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sendSignalLocked t sig info type
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendSignalLocked_sameSnapshot t sig info type).wp P

theorem doSendSigInfo_sameSnapshot (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) : SameSnapshot (doSendSigInfo t sig info type) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.doSendSigInfo_sameWGKernel t sig info type)

theorem doSendSigInfo_spec (P : Snapshot → Prop) (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ doSendSigInfo t sig info type
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (doSendSigInfo_sameSnapshot t sig info type).wp P

theorem sendSigInfo_sameSnapshot (t : TaskRef) (sig : Nat) (info : SigInfo) : SameSnapshot (sendSigInfo t sig info) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.sendSigInfo_sameWGKernel t sig info)

theorem sendSigInfo_spec (P : Snapshot → Prop) (t : TaskRef) (sig : Nat) (info : SigInfo) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sendSigInfo t sig info
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendSigInfo_sameSnapshot t sig info).wp P

theorem sendSig_sameSnapshot (t : TaskRef) (sig priv : Nat) : SameSnapshot (sendSig t sig priv) :=
  sameSnapshot_of_sameWGKernel (SignalFrames.sendSig_sameWGKernel t sig priv)

theorem sendSig_spec (P : Snapshot → Prop) (t : TaskRef) (sig priv : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ sendSig t sig priv
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendSig_sameSnapshot t sig priv).wp P

theorem timestampTruncate_sameSnapshot (t : Timespec64) : SameSnapshot (timestampTruncate t) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.timestampTruncate_sameWGKernel t)

theorem timestampTruncate_spec (P : Snapshot → Prop) (t : Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ timestampTruncate t
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timestampTruncate_sameSnapshot t).wp P

theorem currentTime_sameSnapshot  : SameSnapshot (currentTime ) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.currentTime_sameWGKernel )

theorem currentTime_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ currentTime
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (currentTime_sameSnapshot ).wp P

theorem timespec64Equal_sameSnapshot (a b : Timespec64) : SameSnapshot (timespec64Equal a b) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.timespec64Equal_sameWGKernel a b)

theorem timespec64Equal_spec (P : Snapshot → Prop) (a b : Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ timespec64Equal a b
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timespec64Equal_sameSnapshot a b).wp P

theorem inodeSetCtimeCurrent_sameSnapshot (id : PipefsInodeId) : SameSnapshot (inodeSetCtimeCurrent id) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.inodeSetCtimeCurrent_sameWGKernel id)

theorem inodeSetCtimeCurrent_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ inodeSetCtimeCurrent id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeSetCtimeCurrent_sameSnapshot id).wp P

theorem markInodeDirty_sameSnapshot (id : PipefsInodeId) (flags : Nat) : SameSnapshot (markInodeDirty id flags) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.markInodeDirty_sameWGKernel id flags)

theorem markInodeDirty_spec (P : Snapshot → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ markInodeDirty id flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (markInodeDirty_sameSnapshot id flags).wp P

theorem inodeUpdateTimestamps_sameSnapshot (id : PipefsInodeId) (flags : Nat) : SameSnapshot (inodeUpdateTimestamps id flags) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.inodeUpdateTimestamps_sameWGKernel id flags)

theorem inodeUpdateTimestamps_spec (P : Snapshot → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ inodeUpdateTimestamps id flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeUpdateTimestamps_sameSnapshot id flags).wp P

theorem genericUpdateTime_sameSnapshot (id : PipefsInodeId) (flags : Nat) : SameSnapshot (genericUpdateTime id flags) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.genericUpdateTime_sameWGKernel id flags)

theorem genericUpdateTime_spec (P : Snapshot → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ genericUpdateTime id flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (genericUpdateTime_sameSnapshot id flags).wp P

theorem inodeUpdateTime_sameSnapshot (id : PipefsInodeId) (flags : Nat) : SameSnapshot (inodeUpdateTime id flags) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.inodeUpdateTime_sameWGKernel id flags)

theorem inodeUpdateTime_spec (P : Snapshot → Prop) (id : PipefsInodeId) (flags : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ inodeUpdateTime id flags
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeUpdateTime_sameSnapshot id flags).wp P

theorem relatimeNeedUpdate_sameSnapshot (now : Timespec64) : SameSnapshot (relatimeNeedUpdate now) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.relatimeNeedUpdate_sameWGKernel now)

theorem relatimeNeedUpdate_spec (P : Snapshot → Prop) (now : Timespec64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ relatimeNeedUpdate now
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (relatimeNeedUpdate_sameSnapshot now).wp P

theorem atimeNeedsUpdate_sameSnapshot (id : PipefsInodeId) : SameSnapshot (atimeNeedsUpdate id) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.atimeNeedsUpdate_sameWGKernel id)

theorem atimeNeedsUpdate_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ atimeNeedsUpdate id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (atimeNeedsUpdate_sameSnapshot id).wp P

theorem touchAtime_sameSnapshot (id : PipefsInodeId) : SameSnapshot (touchAtime id) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.touchAtime_sameWGKernel id)

theorem touchAtime_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ touchAtime id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (touchAtime_sameSnapshot id).wp P

theorem fileAccessed_sameSnapshot (f : File) : SameSnapshot (fileAccessed f) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.fileAccessed_sameWGKernel f)

theorem fileAccessed_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ fileAccessed f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileAccessed_sameSnapshot f).wp P

theorem inodeNeedsUpdateTime_sameSnapshot (id : PipefsInodeId) : SameSnapshot (inodeNeedsUpdateTime id) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.inodeNeedsUpdateTime_sameWGKernel id)

theorem inodeNeedsUpdateTime_spec (P : Snapshot → Prop) (id : PipefsInodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ inodeNeedsUpdateTime id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inodeNeedsUpdateTime_sameSnapshot id).wp P

theorem fileUpdateTime_sameSnapshot (f : File) : SameSnapshot (fileUpdateTime f) :=
  sameSnapshot_of_sameWGKernel (Framing.PipeAux.fileUpdateTime_sameWGKernel f)

theorem fileUpdateTime_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ fileUpdateTime f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fileUpdateTime_sameSnapshot f).wp P

end Leanux.Proofs.WG.Keypairs.PipeAux
