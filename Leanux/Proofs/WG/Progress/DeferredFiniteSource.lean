import Leanux.Proofs.WG.Progress.DeferredFiniteNativeSource
import Leanux.Proofs.WG.Progress.TimerFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DeferredFinite
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.TimerDiscipline

theorem hooks_erases : Noise.DriverTags.Deferred.HookErases hooks := by
  constructor
  · change ErasesPrefix (liftPrefix sendOne) Env.runOneSendWorker
    rw [sendOne_source]
    exact erasesPrefix_lift _
  · exact erasesPrefix_lift _
  · intro w pid timer entry prior
    change ErasesPrefix (liftPrefix (TimerFinite.dispatch w pid timer entry prior)) _
    rw [TimerFinite.dispatch_source]
    exact erasesPrefix_lift _
  · intro j
    change ErasesPrefix (liftPrefix (TimerFinite.placeholder j)) _
    rw [TimerFinite.placeholder_source]
    exact erasesPrefix_lift _

def afterXmit : PrefixM PUnit Unit :=
  RxHistory.DeferredSource.afterXmitWith (fun {_} a=>HookScheduler.old a) crypt sendAll

theorem afterXmit_erases : ErasesPrefix afterXmit Env.afterXmit :=
  Noise.DriverTags.Deferred.afterXmit_erases _ HookDeferred.quiet_erases _ _ crypt_erases sendAll_erases

def timers (j : UInt64) : PrefixM PUnit Bool :=
  Noise.DriverTags.Deferred.timersWith (fun {_} a=>HookScheduler.old a) hooks crypt j

theorem timers_erases (j : UInt64) : ErasesPrefix (timers j) (Env.runTimers j) :=
  Noise.DriverTags.Deferred.timers_erases _ HookDeferred.quiet_erases _ hooks_erases _ crypt_erases j

def placeholder (j : UInt64) : PrefixM PUnit Unit :=
  Noise.DriverTags.Deferred.placeholderWith (fun {_} a=>HookScheduler.old a) hooks crypt sendAll j

theorem placeholder_erases (j : UInt64) : ErasesPrefix (placeholder j) (Env.runTimersPlaceholder j) :=
  Noise.DriverTags.Deferred.placeholder_erases _ HookDeferred.quiet_erases _ hooks_erases _ _ crypt_erases sendAll_erases j

def idle : PrefixM PUnit Unit :=
  RxHistory.DeferredSource.idleWith (fun {_} a=>HookScheduler.old a) timers placeholder

theorem idle_erases : ErasesPrefix idle Env.idleTimers :=
  Noise.DriverTags.Deferred.idle_erases _ HookDeferred.quiet_erases _ _ timers_erases placeholder_erases

def afterAdvance : PrefixM PUnit Unit :=
  RxHistory.DeferredSource.afterAdvanceWith (fun {_} a=>HookScheduler.old a) timers placeholder

theorem afterAdvance_erases : ErasesPrefix afterAdvance Env.afterAdvance :=
  Noise.DriverTags.Deferred.afterAdvance_erases _ HookDeferred.quiet_erases _ _ timers_erases placeholder_erases

/-- Every existing deferred constructor, composed with concrete finite callbacks. -/
def observed (call : EnvDeferredCall) : PrefixM PUnit call.Result :=
  Noise.DriverTags.Deferred.deferredWith (fun {_} a=>HookScheduler.old a)
    hooks crypt sendAll afterXmit timers placeholder idle afterAdvance call

theorem observed_erases (call : EnvDeferredCall) : ErasesPrefix (observed call) call.original :=
  Noise.DriverTags.Deferred.deferred_erases _ HookDeferred.quiet_erases _ hooks_erases
    _ _ _ _ _ _ _ crypt_erases sendAll_erases afterXmit_erases timers_erases placeholder_erases
    idle_erases afterAdvance_erases call

/-- Empty-journal evaluation of the existing finite concrete factory. -/
def evaluate (call : EnvDeferredCall) : Leanux.M call.Result :=
  fun w => (runPrefix (observed call) w []).1

theorem evaluate_source (call : EnvDeferredCall) : call.original = evaluate call := by
  funext w
  exact (observed_erases call w []).symm

end Leanux.Proofs.WG.Progress.DeferredFinite
