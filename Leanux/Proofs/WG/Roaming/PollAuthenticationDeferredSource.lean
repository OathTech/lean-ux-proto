import Leanux.Proofs.WG.Roaming.PollAuthenticationSchedulerSource
import Leanux.Proofs.WG.Roaming.PollAuthenticationSavedSource
import Leanux.Proofs.WG.Index.DeferredSavedSource
import Leanux.Proofs.WG.Noise.DriverTagDeferredSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication.Deferred
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes

theorem sendOne : PrefixPreserves Reached PublicSafe (RxHistory.audit runOneSendWorkerAudit) :=
  audit _ PublicationDeferred.sendOne

theorem clearOne : PrefixPreserves Reached PublicSafe (RxHistory.audit runOneClearWorkerAudit) :=
  audit _ PublicationDeferred.clearOne

theorem drained (what : String) (flags : List Bool) :
    PrefixPreserves Reached PublicSafe (RxHistory.mixed (requireDrainedPrefix what flags)) :=
  mixed _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationDeferred.«0».Leanux.Proofs.WG.PublicationDeferred.drained) what flags)

theorem hooks : Noise.DriverTags.Deferred.HookContracts Reached PublicSafe
    (Noise.DriverTags.Deferred.originalHooks (fun {_} action => action)) :=
  ⟨sendOne,clearOne,
    fun worker pid timer entry prior => audit _ (PublicationAudited.timerDispatch worker pid timer entry prior),
    fun j => audit _ (PublicationAudited.placeholderPass j)⟩

theorem stepComplete (bucket : UInt64) :
    PrefixPreserves Reached PublicSafe (RxHistory.audit (requireStepCompleteAudit bucket)) :=
  audit _ (PublicationAudited.stepComplete bucket)

theorem nothingDue (j : UInt64) :
    PrefixPreserves Reached PublicSafe (RxHistory.audit (requireNothingDueAudit j)) :=
  audit _ (PublicationAudited.nothingDue j)

theorem crypt : PrefixPreserves Reached PublicSafe RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves reached_safe reached_store _ (schedule none)

theorem send : PrefixPreserves Reached PublicSafe RxHistory.runSendWorkers := by
  rw [RxHistory.DeferredSource.send_factor, ←Noise.DriverTags.Deferred.send_source]
  exact Noise.DriverTags.Deferred.send_preserves reached_safe reached_store _ hooks _ (schedule none)

theorem afterXmit : PrefixPreserves Reached PublicSafe RxHistory.afterXmit := by
  rw [RxHistory.DeferredSource.afterXmit_factor]
  exact Noise.DriverTags.Deferred.afterXmit_preserves_drained reached_safe reached_store _
    drained _ _ crypt send

theorem timers (j : UInt64) :
    PrefixPreserves Reached PublicSafe (RxHistory.runTimers j) :=
  Index.DeferredRules.runTimers_preserves_saved_variant reached_safe reached_store
    saved_spec wheel_spec hooks.timer stepComplete sendOne clearOne crypt j

theorem placeholder (j : UInt64) :
    PrefixPreserves Reached PublicSafe (RxHistory.runTimersPlaceholder j) := by
  rw [RxHistory.DeferredSource.placeholder_factor, ←Noise.DriverTags.Deferred.placeholder_source]
  exact Noise.DriverTags.Deferred.placeholder_preserves_saved reached_safe reached_store _
    ((saved_spec.consequence (fun _ _ pre=>pre) (fun _ _ _ post=>post.1)).preserves)
    _ hooks _ _ crypt send j

theorem idle : PrefixPreserves Reached PublicSafe RxHistory.idleTimers := by
  rw [RxHistory.DeferredSource.idle_factor]
  exact Noise.DriverTags.Deferred.idle_preserves_nothingDue reached_safe reached_store _
    nothingDue _ _ timers placeholder

theorem afterAdvance : PrefixPreserves Reached PublicSafe RxHistory.afterAdvance := by
  rw [RxHistory.DeferredSource.afterAdvance_factor]
  exact Noise.DriverTags.Deferred.afterAdvance_preserves_nothingDue reached_safe reached_store _
    nothingDue _ _ timers placeholder

theorem deferred (call : EnvDeferredCall) :
    PrefixPreserves Reached PublicSafe (RxHistory.deferred call) := by
  cases call with
  | drained what flags => exact drained what flags
  | idleDevice => exact mixed _ (PublicationDeferred.deferred .idleDevice)
  | noCrypt => exact audit _ (PublicationDeferred.deferred .noCrypt)
  | crypt => exact crypt
  | sendOne => exact sendOne
  | clearOne => exact clearOne
  | sendAll => exact send
  | afterXmit => exact afterXmit
  | timerWorker timer => exact audit _ (PublicationDeferred.deferred (.timerWorker timer))
  | timers j => exact timers j
  | placeholder j => exact placeholder j
  | idle => exact idle
  | advance ticks => exact audit _ (PublicationDeferred.deferred (.advance ticks))
  | afterAdvance => exact afterAdvance

end Leanux.Proofs.WG.Roaming.PollAuthentication.Deferred
