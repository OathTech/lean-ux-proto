import Leanux.Proofs.WG.Roaming.PollAuthenticationWorkersSource
import Leanux.Proofs.WG.Packets.PublicationEnvironment
import Leanux.Proofs.WG.Queues.SchedulerPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes
variable {α : Type}

theorem scheduler_atoms :
    RxHistory.SchedulerSource.AtomContracts Reached PublicSafe (fun {_} action => action) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α action
    apply mixed
    exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.mixed_lift)
      (monadLift action : Leanux.M α)
      (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))
  · intro α stop
    exact mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.mixed_throw) stop)
  · intro pid
    exact mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.peer) pid)
  · intro id
    exact mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.packet) id)
  · intro f
    exact mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.work) f)
  · intro a
    exact mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.occupancy) a)
  · intro next
    exact mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.pendingNapi) next)
  · intro a
    exact mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.hasWork) a)
  · exact audit _ PublicationJoint.filter_probe

theorem cryptAhead (pid : PeerId) :
    PrefixPreserves Reached PublicSafe (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves reached_safe _ scheduler_atoms _ encryptIteration pid

theorem activationIteration (a : Activation) :
    PrefixPreserves Reached PublicSafe (RxHistory.activationIteration a) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ scheduler_atoms _ _ _ _ _
    encryptIteration cryptAhead txIteration decryptIteration receiveIteration a

theorem activationRun (a : Activation) :
    PrefixPreserves Reached PublicSafe (RxHistory.activationRun a) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves reached_safe reached_store _ scheduler_atoms _
    activationIteration a

theorem dispatch (worker : Worker) :
    PrefixPreserves Reached PublicSafe (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves reached_safe reached_store _ scheduler_atoms _
    activationRun worker

theorem schedule (stack : Option Worker) :
    PrefixPreserves Reached PublicSafe (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves reached_safe reached_store _ scheduler_atoms _ _ _
    dispatch activationRun napiSoftirq stack

theorem nestedResched (worker : Worker) :
    PrefixPreserves Reached PublicSafe (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves reached_safe reached_store _ schedule worker

end Leanux.Proofs.WG.Roaming.PollAuthentication
