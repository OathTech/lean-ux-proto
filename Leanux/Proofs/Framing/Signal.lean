import Leanux.Proofs.Framing.Kernel
import Leanux.Kernel.Signal

/-! Shared full WireGuard frames for the original task and signal helpers. -/
namespace Leanux.Proofs.Framing.SignalFrames
open Leanux Std.Do Leanux.Proofs.Framing.KernelFrames
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem getTask_sameWGKernel (t : TaskRef) : SameWGKernel (getTask t) := by
  frame_wg [getTask] using []

theorem getTask_spec (P : WGKernelView → Prop) (t : TaskRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ getTask t
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getTask_sameWGKernel t).wp P

theorem modifyTask_sameWGKernel (t : TaskRef) (f : Task → Task) : SameWGKernel (modifyTask t f) := by
  frame_wg [modifyTask] using []

theorem modifyTask_spec (P : WGKernelView → Prop) (t : TaskRef) (f : Task → Task) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ modifyTask t f
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (modifyTask_sameWGKernel t f).wp P

theorem getCurrent_sameWGKernel  : SameWGKernel (getCurrent ) := by
  frame_wg [getCurrent] using [getTask_spec]

theorem getCurrent_spec (P : WGKernelView → Prop)  :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ getCurrent
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (getCurrent_sameWGKernel ).wp P

theorem sigqueueAlloc_sameWGKernel (overrideRlimit : Nat) : SameWGKernel (sigqueueAlloc overrideRlimit) := by
  frame_wg [sigqueueAlloc] using [envOk_spec]

theorem sigqueueAlloc_spec (P : WGKernelView → Prop) (overrideRlimit : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ sigqueueAlloc overrideRlimit
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sigqueueAlloc_sameWGKernel overrideRlimit).wp P

theorem sigDisposition_sameWGKernel (tk : Task) (sig : Nat) : SameWGKernel (sigDisposition tk sig) := by
  frame_wg [sigDisposition] using []

theorem sigDisposition_spec (P : WGKernelView → Prop) (tk : Task) (sig : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ sigDisposition tk sig
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sigDisposition_sameWGKernel tk sig).wp P

theorem sigHandlerIgnored_sameWGKernel (disp : SigDisposition) (sig : Nat) : SameWGKernel (sigHandlerIgnored disp sig) := by
  frame_wg [sigHandlerIgnored] using []

theorem sigHandlerIgnored_spec (P : WGKernelView → Prop) (disp : SigDisposition) (sig : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ sigHandlerIgnored disp sig
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sigHandlerIgnored_sameWGKernel disp sig).wp P

theorem sigTaskIgnored_sameWGKernel (t : TaskRef) (sig : Nat) (force : Bool) : SameWGKernel (sigTaskIgnored t sig force) := by
  frame_wg [sigTaskIgnored] using [getTask_spec, sigDisposition_spec, sigHandlerIgnored_spec]

theorem sigTaskIgnored_spec (P : WGKernelView → Prop) (t : TaskRef) (sig : Nat) (force : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ sigTaskIgnored t sig force
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sigTaskIgnored_sameWGKernel t sig force).wp P

theorem sigIgnored_sameWGKernel (t : TaskRef) (sig : Nat) (force : Bool := false) : SameWGKernel (sigIgnored t sig force) := by
  frame_wg [sigIgnored] using [getTask_spec, sigTaskIgnored_spec]

theorem sigIgnored_spec (P : WGKernelView → Prop) (t : TaskRef) (sig : Nat) (force : Bool := false) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ sigIgnored t sig force
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sigIgnored_sameWGKernel t sig force).wp P

theorem prepareSignal_sameWGKernel (t : TaskRef) (sig : Nat) (force : Bool := false) : SameWGKernel (prepareSignal t sig force) := by
  frame_wg [prepareSignal] using [sigIgnored_spec]

theorem prepareSignal_spec (P : WGKernelView → Prop) (t : TaskRef) (sig : Nat) (force : Bool := false) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ prepareSignal t sig force
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (prepareSignal_sameWGKernel t sig force).wp P

theorem legacyQueue_sameWGKernel (pending : SigSet) (sig : Nat) : SameWGKernel (legacyQueue pending sig) := by
  frame_wg [legacyQueue] using []

theorem legacyQueue_spec (P : WGKernelView → Prop) (pending : SigSet) (sig : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ legacyQueue pending sig
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (legacyQueue_sameWGKernel pending sig).wp P

theorem wantsSignal_sameWGKernel (t : TaskRef) (sig : Nat) : SameWGKernel (wantsSignal t sig) := by
  frame_wg [wantsSignal] using [getTask_spec]

theorem wantsSignal_spec (P : WGKernelView → Prop) (t : TaskRef) (sig : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ wantsSignal t sig
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (wantsSignal_sameWGKernel t sig).wp P

theorem signalWakeUpState_sameWGKernel (t : TaskRef) : SameWGKernel (signalWakeUpState t) := by
  frame_wg [signalWakeUpState] using [modifyTask_spec]

theorem signalWakeUpState_spec (P : WGKernelView → Prop) (t : TaskRef) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ signalWakeUpState t
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (signalWakeUpState_sameWGKernel t).wp P

theorem completeSignal_sameWGKernel (t : TaskRef) (sig type : Nat) : SameWGKernel (completeSignal t sig type) := by
  frame_wg [completeSignal] using [wantsSignal_spec, getTask_spec, sigDisposition_spec, signalWakeUpState_spec]

theorem completeSignal_spec (P : WGKernelView → Prop) (t : TaskRef) (sig type : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ completeSignal t sig type
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (completeSignal_sameWGKernel t sig type).wp P

theorem sendSignalLocked'_sameWGKernel (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) (force : Bool) : SameWGKernel (sendSignalLocked' t sig info type force) := by
  frame_wg [sendSignalLocked'] using [prepareSignal_spec, legacyQueue_spec, sigqueueAlloc_spec, completeSignal_spec, getTask_spec, modifyTask_spec]

theorem sendSignalLocked'_spec (P : WGKernelView → Prop) (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) (force : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ sendSignalLocked' t sig info type force
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sendSignalLocked'_sameWGKernel t sig info type force).wp P

theorem sendSignalLocked_sameWGKernel (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) : SameWGKernel (sendSignalLocked t sig info type) := by
  frame_wg [sendSignalLocked] using [sendSignalLocked'_spec]

theorem sendSignalLocked_spec (P : WGKernelView → Prop) (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ sendSignalLocked t sig info type
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sendSignalLocked_sameWGKernel t sig info type).wp P

theorem doSendSigInfo_sameWGKernel (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) : SameWGKernel (doSendSigInfo t sig info type) := by
  frame_wg [doSendSigInfo] using [sendSignalLocked_spec]

theorem doSendSigInfo_spec (P : WGKernelView → Prop) (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ doSendSigInfo t sig info type
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (doSendSigInfo_sameWGKernel t sig info type).wp P

theorem sendSigInfo_sameWGKernel (t : TaskRef) (sig : Nat) (info : SigInfo) : SameWGKernel (sendSigInfo t sig info) := by
  frame_wg [sendSigInfo] using [doSendSigInfo_spec]

theorem sendSigInfo_spec (P : WGKernelView → Prop) (t : TaskRef) (sig : Nat) (info : SigInfo) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ sendSigInfo t sig info
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sendSigInfo_sameWGKernel t sig info).wp P

theorem sendSig_sameWGKernel (t : TaskRef) (sig priv : Nat) : SameWGKernel (sendSig t sig priv) := by
  frame_wg [sendSig] using [sendSigInfo_spec]

theorem sendSig_spec (P : WGKernelView → Prop) (t : TaskRef) (sig priv : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ sendSig t sig priv
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (sendSig_sameWGKernel t sig priv).wp P

theorem forceSigInfoToTask_sameWGKernel (info : SigInfo) (t : TaskRef) (handler : Nat) : SameWGKernel (forceSigInfoToTask info t handler) := by
  frame_wg [forceSigInfoToTask] using [getTask_spec, modifyTask_spec, sendSignalLocked_spec, signalWakeUpState_spec]

theorem forceSigInfoToTask_spec (P : WGKernelView → Prop) (info : SigInfo) (t : TaskRef) (handler : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ forceSigInfoToTask info t handler
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (forceSigInfoToTask_sameWGKernel info t handler).wp P

theorem forceSigSeccomp_sameWGKernel (syscall data : Int) (forceCoredump : Bool) : SameWGKernel (forceSigSeccomp syscall data forceCoredump) := by
  frame_wg [forceSigSeccomp] using [forceSigInfoToTask_spec]

theorem forceSigSeccomp_spec (P : WGKernelView → Prop) (syscall data : Int) (forceCoredump : Bool) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ forceSigSeccomp syscall data forceCoredump
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (forceSigSeccomp_sameWGKernel syscall data forceCoredump).wp P

end Leanux.Proofs.Framing.SignalFrames
