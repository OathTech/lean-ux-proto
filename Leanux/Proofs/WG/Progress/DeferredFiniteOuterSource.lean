import Leanux.Proofs.WG.Progress.DeferredFiniteNativeSource
import Leanux.Proofs.WG.TimerDiscipline.WheelDispatchSource
import Leanux.Proofs.WG.Progress.AdvanceWaitSource
import Leanux.Proofs.WG.Progress.DeferredOuterFactors

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DeferredFinite
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged
open Leanux.Proofs.WG.TimerDiscipline

def nativeCrypt : Leanux.M Unit := fun w => (runPrefix crypt w []).1
theorem nativeCrypt_source : Env.runCryptWorkers = nativeCrypt := by
  funext w
  exact (crypt_erases w []).symm

def nativeSendAll : Leanux.M Unit := fun w => (runPrefix sendAll w []).1
theorem nativeSendAll_source : Env.runSendWorkers = nativeSendAll := by
  funext w
  exact (sendAll_erases w []).symm

def nativeTimers (j : UInt64) : Leanux.M Bool :=
  runTimersWheelWith TimerFinite.dispatch sendOne nativeCrypt j

theorem nativeTimers_source (j : UInt64) : Env.runTimers j = nativeTimers j := by
  rw [← runTimers_wheel_source]
  change runTimersWheelWith timerDispatchUnit_variant Env.runOneSendWorker Env.runCryptWorkers j = _
  unfold nativeTimers
  have sameDispatch : timerDispatchUnit_variant = TimerFinite.dispatch := by
    funext w pid timer entry prior
    exact TimerFinite.dispatch_source w pid timer entry prior
  rw [sameDispatch, sendOne_source, nativeCrypt_source]

end Leanux.Proofs.WG.Progress.DeferredFinite

namespace Leanux.Proofs.WG.Progress.DeferredFinite
open Leanux Leanux.WG Leanux.Env
def nativePlaceholder (j : UInt64) : Leanux.M Unit :=
  Noise.DriverTags.Deferred.placeholderWithNative (fun {_} a => a) (liftWG getDev)
    TimerFinite.placeholder nativeCrypt nativeSendAll Env.runOneClearWorker j

theorem nativePlaceholder_source (j : UInt64) :
    Env.runTimersPlaceholder j = nativePlaceholder j := by
  unfold nativePlaceholder
  rw [← nativeCrypt_source, ← nativeSendAll_source]
  have same : WG.timerCallback = TimerFinite.callback := funext fun pid => funext (TimerFinite.callback_source pid)
  unfold Noise.DriverTags.Deferred.placeholderWithNative TimerFinite.placeholder
  rw [← same]
  simp only [Env.runTimersPlaceholder, bind_assoc, pure_bind]
  rfl
end Leanux.Proofs.WG.Progress.DeferredFinite

namespace Leanux.Proofs.WG.Progress.DeferredFinite
open Leanux Leanux.WG Leanux.Env

def nativeAfterXmit : Leanux.M Unit := DeferredOuter.afterXmitWith nativeCrypt nativeSendAll
theorem nativeAfterXmit_source : Env.afterXmit = nativeAfterXmit := by
  rw [DeferredOuter.afterXmit_source, nativeCrypt_source, nativeSendAll_source]
  rfl

def nativeIdle : Leanux.M Unit := DeferredOuter.idleWith nativeTimers nativePlaceholder
theorem nativeIdle_source : Env.idleTimers = nativeIdle := by
  rw [DeferredOuter.idle_source]
  have timersSame : Env.runTimers = nativeTimers := funext nativeTimers_source
  have placeSame : Env.runTimersPlaceholder = nativePlaceholder := funext nativePlaceholder_source
  rw [timersSame, placeSame]
  rfl

def nativeAfterAdvance : Leanux.M Unit :=
  afterAdvancePrefixWith nativeTimers nativePlaceholder >>= afterAdvanceSuffixWith nativeTimers

theorem nativeAfterAdvance_source : Env.afterAdvance = nativeAfterAdvance := by
  rw [afterAdvance_source]
  have pre : afterAdvancePrefix = afterAdvancePrefixWith Env.runTimers Env.runTimersPlaceholder := rfl
  have suf : afterAdvanceSuffix = afterAdvanceSuffixWith Env.runTimers := rfl
  rw [pre, suf]
  have timersSame : Env.runTimers = nativeTimers := funext nativeTimers_source
  have placeSame : Env.runTimersPlaceholder = nativePlaceholder := funext nativePlaceholder_source
  rw [timersSame, placeSame]
  rfl
end Leanux.Proofs.WG.Progress.DeferredFinite

namespace Leanux.Proofs.WG.Progress.DeferredFinite
open Leanux Leanux.WG Leanux.Proofs.Logged

def afterXmit : PrefixM PUnit Unit := liftPrefix (nativeAfterXmit)

theorem afterXmit_erases : ErasesPrefix afterXmit Env.afterXmit := by
  unfold afterXmit
  rw [nativeAfterXmit_source]
  exact erasesPrefix_lift _

def timers (j : UInt64) : PrefixM PUnit Bool := liftPrefix (nativeTimers j)

theorem timers_erases (j : UInt64) : ErasesPrefix (timers j) (Env.runTimers j) := by
  unfold timers
  rw [nativeTimers_source j]
  exact erasesPrefix_lift _

def placeholder (j : UInt64) : PrefixM PUnit Unit := liftPrefix (nativePlaceholder j)

theorem placeholder_erases (j : UInt64) : ErasesPrefix (placeholder j) (Env.runTimersPlaceholder j) := by
  unfold placeholder
  rw [nativePlaceholder_source j]
  exact erasesPrefix_lift _

def idle : PrefixM PUnit Unit := liftPrefix (nativeIdle)

theorem idle_erases : ErasesPrefix idle Env.idleTimers := by
  unfold idle
  rw [nativeIdle_source]
  exact erasesPrefix_lift _

def afterAdvance : PrefixM PUnit Unit := liftPrefix (nativeAfterAdvance)

theorem afterAdvance_erases : ErasesPrefix afterAdvance Env.afterAdvance := by
  unfold afterAdvance
  rw [nativeAfterAdvance_source]
  exact erasesPrefix_lift _


end Leanux.Proofs.WG.Progress.DeferredFinite
