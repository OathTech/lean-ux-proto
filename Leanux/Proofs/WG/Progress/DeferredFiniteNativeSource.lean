import Leanux.Proofs.WG.Progress.TimerFiniteNativeSource
import Leanux.Proofs.WG.Progress.SchedulerFiniteSource
import Leanux.Proofs.WG.Progress.InitiationCallerFiniteSource
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource
import Leanux.Proofs.WG.Noise.DriverTagDeferredFactors

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DeferredFinite
open Leanux Leanux.WG Leanux.Proofs.Logged
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


def schedule : PrefixM PUnit Unit := liftPrefix (SchedulerFinite.schedule none)

theorem schedule_erases : ErasesPrefix schedule (Env.schedule none) := by
  unfold schedule
  rw [SchedulerFinite.schedule_source]
  exact erasesPrefix_lift _


def crypt : PrefixM PUnit Unit := do
  schedule
  liftPrefix Env.deliverSent

theorem crypt_erases : ErasesPrefix crypt Env.runCryptWorkers := by
  unfold crypt Env.runCryptWorkers
  exact erasesPrefix_bind schedule_erases (fun _ => erasesPrefix_lift _)

def sendAll : PrefixM PUnit Unit := Noise.DriverTags.Deferred.sendWith hooks schedule

theorem sendAll_erases : ErasesPrefix sendAll Env.runSendWorkers :=
  Noise.DriverTags.Deferred.send_erases_native hooks
    (by change ErasesPrefix (liftPrefix sendOne) Env.runOneSendWorker
        rw [sendOne_source]
        exact erasesPrefix_lift _)
    schedule schedule_erases

end Leanux.Proofs.WG.Progress.DeferredFinite
