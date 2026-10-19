import Leanux.Proofs.WG.Progress.TimerFiniteSource
import Leanux.Proofs.WG.Progress.SchedulerFiniteSource
import Leanux.Proofs.WG.Progress.InitiationCallerFiniteSource
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DeferredFinite
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.TimerDiscipline

/-- Native selection/dequeue and worker section with finite handshake sending. -/
def sendOne : Leanux.M Unit := do
  let selected ← sendWorkerSelection
  sendWorkerDequeue selected.2
  Env.runWorker .sendWorker (HandshakeFinite.sendWorker selected.2)

theorem sendOne_source : Env.runOneSendWorker = sendOne := by
  rw [runOneSendWorker_source]
  unfold sendOne
  simp only [HandshakeFinite.sendWorker_source]

def hooks : Noise.DriverTags.Deferred.Hooks PUnit :=
  ⟨liftPrefix sendOne, liftPrefix Env.runOneClearWorker,
    fun w pid timer entry prior=>liftPrefix (TimerFinite.dispatch w pid timer entry prior),
    fun j=>liftPrefix (TimerFinite.placeholder j)⟩

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

def schedule : PrefixM PUnit Unit := liftPrefix (SchedulerFinite.schedule none)

theorem schedule_erases : ErasesPrefix schedule (Env.schedule none) := by
  unfold schedule
  rw [SchedulerFinite.schedule_source]
  exact erasesPrefix_lift _

def crypt : PrefixM PUnit Unit := RxHistory.DeferredSource.cryptWith schedule

theorem crypt_erases : ErasesPrefix crypt Env.runCryptWorkers :=
  Noise.DriverTags.Deferred.crypt_erases _ schedule_erases

def sendAll : PrefixM PUnit Unit := Noise.DriverTags.Deferred.sendWith hooks schedule

theorem sendAll_erases : ErasesPrefix sendAll Env.runSendWorkers :=
  Noise.DriverTags.Deferred.send_erases _ hooks_erases _ schedule_erases

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
