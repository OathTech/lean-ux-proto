import Leanux.Proofs.WG.Roaming.RemoteDriverPollSource
import Leanux.Proofs.WG.Roaming.RemoteDriverCaptureSource
import Leanux.Proofs.WG.Queues.RxWaitAppends
import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Queues.DeferredPreservation
import Leanux.Proofs.WG.Index.TimerProductRulesSource
import Leanux.Proofs.WG.Queues.SendEnvironment
import Leanux.Proofs.WG.Queues.EnvClearDispatch
import Leanux.Proofs.WG.Roaming.RemoteDriverFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Roaming.RemoteDriver
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem projection_erases {α : Type} {observed : PrefixM Event α}
    {old : RxHistory.Obs α} {native : Leanux.M α}
    (project : ProjectsPrefix rxEvent id observed old) (erase : ErasesPrefix old native) :
    ErasesPrefix observed native := by
  intro w history
  have same := congrArg Prod.fst (project w history)
  rw [erase w (history.filterMap rxEvent)] at same
  cases result : (runPrefix observed w history).1 <;> simpa [result,Except.map] using same.symm
end Leanux.Proofs.WG.Roaming.RemoteDriver

namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Scheduler
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem atoms (entry : RemoteMap) :
    RxHistory.SchedulerSource.AtomContracts (Inv entry) Safe (fun {_} a => focus a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact focus_store entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (erasesPrefix_lift _))
      (fun _ => productAmbient_spec a _ (fun _ _ hi=>hi))
  · intro α stop
    exact focus_store entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (erasesPrefix_throw stop)) (fun _=>hoare_throw stop)
  · intro pid
    exact focus_native entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (getPeerMixed_erases pid)))
      (fun before=>RemoteSilent.of_frame before _ (RemoteSilent.getPeer_frame pid))
  · intro id
    exact focus_native entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (getTxSkbPrefix_erases id)))
      (fun before=>RemoteSilent.of_frame before _ (RemoteWorkers.packet_frame (SkbStore.getTx id)))
  · intro f
    exact focus_native entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _)))
      (fun before=>RemoteSilent.of_frame before _ (modifyDev_remotes
        (fun d=>{d with txWorkQueue:=f d.txWorkQueue}) (fun _=>rfl)))
  · intro a
    exact focus_store entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (activationOccupancyPrefix_erases a))
      (activationOccupancy_sameKernel a)
  · intro next
    exact focus_store entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (pendingNapiPrefix_erases next))
      (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact focus_store entry _ _ (Appends.focus _ _ _)
      (RxHistory.mixed_erases (activationHasWorkPrefix_erases a))
      (activationHasWork_sameKernel a)
  · apply focus_store entry _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases consistentFilterAudit_erases)
    exact (show SameProductStore getAmbient from fun initial=>
      productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi=>hi)).bind
        (fun w=>filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)

theorem focus_projects {α : Type} (action : RxHistory.Obs α) (appends : Appends action) :
    ProjectsPrefix rxEvent id (focus action) action :=
  appends.project_focus Event.rx rxEvent (fun _=>rfl)

def tx (pid : PeerId) : PrefixM Event IterResult :=
  focus (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker))))

theorem tx_preserves (entry : RemoteMap) (pid : PeerId) :
    PrefixPreserves (Inv entry) Safe (tx pid) :=
  focus_retained entry _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (txIterPrefix_erases _ (erasesPrefix_lift _)))
    (fun before=>RemoteWorkers.txIter before pid)

theorem tx_projects (pid : PeerId) : ProjectsPrefix rxEvent id (tx pid)
    (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  focus_projects _ (Appends.focus _ _ _)

end Leanux.Proofs.WG.Roaming.RemoteDriver.Scheduler




namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Scheduler
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open RxHistory.SchedulerSource

def encrypt : PrefixM Event IterResult := focus RxHistory.encryptIteration
def decrypt : PrefixM Event IterResult := focus RxHistory.decryptIteration
def napi : PrefixM Event Unit := focus RxHistory.napiSoftirq
def ahead (pid : PeerId) : PrefixM Event Unit := cryptAheadWith (fun {_} g=>focus g) encrypt pid
def iteration (a : Activation) : PrefixM Event IterResult :=
  iterationWith (fun {_} g=>focus g) encrypt ahead tx decrypt receiveIterationObserved a
def run (a : Activation) : PrefixM Event Unit := runWith (fun {_} g=>focus g) iteration a
def dispatch (worker : Worker) : PrefixM Event Bool := dispatchWith (fun {_} g=>focus g) run worker
def schedule (stack : Option Worker := none) : PrefixM Event Unit :=
  scheduleWith (fun {_} g=>focus g) dispatch run napi stack
def nested (worker : Worker) : PrefixM Event Unit := nestedWith (fun stack=>schedule stack) worker

theorem encrypt_projects : ProjectsPrefix rxEvent id encrypt RxHistory.encryptIteration :=
  focus_projects _ (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptIteration_appends)
theorem decrypt_projects : ProjectsPrefix rxEvent id decrypt RxHistory.decryptIteration :=
  focus_projects _ (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.decryptIteration_appends)
theorem napi_projects : ProjectsPrefix rxEvent id napi RxHistory.napiSoftirq :=
  focus_projects _ RxHistory.napiSoftirq_appends

theorem ahead_projects (pid : PeerId) : ProjectsPrefix rxEvent id (ahead pid) (RxHistory.cryptAhead pid) :=
  cryptAhead_projects rxEvent _ (fun {_} g=>g) (fun g ha=>focus_projects g ha)
    _ _ encrypt_projects pid

theorem iteration_projects (a : Activation) :
    ProjectsPrefix rxEvent id (iteration a) (RxHistory.activationIteration a) :=
  RxHistory.SchedulerSource.iteration_projects rxEvent _ (fun {_} g=>g) (fun g ha=>focus_projects g ha)
    _ _ _ _ _ _ _ _ _ _ encrypt_projects ahead_projects tx_projects decrypt_projects receiveIteration_projects a

theorem run_projects (a : Activation) :
    ProjectsPrefix rxEvent id (run a) (RxHistory.activationRun a) :=
  RxHistory.SchedulerSource.run_projects rxEvent _ (fun {_} g=>g) (fun g ha=>focus_projects g ha)
    _ _ iteration_projects a

theorem dispatch_projects (worker : Worker) :
    ProjectsPrefix rxEvent id (dispatch worker) (RxHistory.dispatch worker) :=
  RxHistory.SchedulerSource.dispatch_projects rxEvent _ (fun {_} g=>g) (fun g ha=>focus_projects g ha)
    _ _ run_projects worker

theorem schedule_projects (stack : Option Worker) :
    ProjectsPrefix rxEvent id (schedule stack) (RxHistory.schedule stack) :=
  RxHistory.SchedulerSource.schedule_projects rxEvent _ (fun {_} g=>g) (fun g ha=>focus_projects g ha)
    _ _ _ _ _ _ dispatch_projects run_projects napi_projects stack

theorem nested_projects (worker : Worker) :
    ProjectsPrefix rxEvent id (nested worker) (RxHistory.nestedResched worker) :=
  RxHistory.SchedulerSource.nested_projects rxEvent _ _ schedule_projects worker

theorem ahead_appends (pid : PeerId) : Appends (ahead pid) :=
  cryptAhead_appends _ (fun g _=>Appends.focus _ _ g) _ (Appends.focus _ _ _) pid

theorem iteration_appends (a : Activation) : Appends (iteration a) :=
  RxHistory.SchedulerSource.iteration_appends _ (fun g _=>Appends.focus _ _ g)
    _ _ _ _ _ (Appends.focus _ _ _) ahead_appends (fun _=>Appends.focus _ _ _)
    (Appends.focus _ _ _) receiveIteration_appends a

theorem run_appends (a : Activation) : Appends (run a) :=
  RxHistory.SchedulerSource.run_appends _ (fun g _=>Appends.focus _ _ g) _ iteration_appends a

theorem dispatch_appends (worker : Worker) : Appends (dispatch worker) :=
  RxHistory.SchedulerSource.dispatch_appends _ (fun g _=>Appends.focus _ _ g) _ run_appends worker

theorem schedule_appends (stack : Option Worker) : Appends (schedule stack) :=
  RxHistory.SchedulerSource.schedule_appends _ (fun g _=>Appends.focus _ _ g)
    _ _ _ dispatch_appends run_appends (Appends.focus _ _ _) stack

theorem nested_appends (worker : Worker) : Appends (nested worker) :=
  RxHistory.SchedulerSource.nested_appends _ schedule_appends worker

theorem schedule_erases (stack : Option Worker) :
    ErasesPrefix (schedule stack) (Env.schedule stack) :=
  projection_erases (schedule_projects stack) (RxHistory.schedule_erases stack)
theorem nested_erases (worker : Worker) :
    ErasesPrefix (nested worker) (Env.nestedResched worker) :=
  projection_erases (nested_projects worker) (RxHistory.nestedResched_erases worker)

end Leanux.Proofs.WG.Roaming.RemoteDriver.Scheduler

namespace Leanux.Proofs.WG.Roaming.RemotePoll
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem encryptIteration_covered (entry : RemoteMap) :
    PrefixPreserves (Covered entry rxCause) (fun _=>True) RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  apply PrefixPreserves.bind (quiet entry rxCause _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _)))
    (fun initial=>PublicationPoll.native_product _ _
      ((RemoteWorkers.encryptPoll_frame).wp (RemoteRetained initial))))
  intro item
  exact (softirq_covered entry).bind (fun _=>quiet entry rxCause _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (RxWorkers.encryptTail_erases item))
    (fun initial=>RemoteWorkers.encryptTail initial item))
end Leanux.Proofs.WG.Roaming.RemotePoll

namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Scheduler
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem encrypt_preserves (entry : RemoteMap) : PrefixPreserves (Inv entry) Safe encrypt :=
  covered_focus entry _ (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptIteration_appends)
    RemotePoll.encryptIteration_covered

theorem decrypt_preserves (entry : RemoteMap) : PrefixPreserves (Inv entry) Safe decrypt :=
  covered_focus entry _ (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.decryptIteration_appends)
    RemotePoll.decryptIteration_covered

theorem napi_preserves (entry : RemoteMap) : PrefixPreserves (Inv entry) Safe napi :=
  covered_focus entry _ RxHistory.napiSoftirq_appends RemotePoll.softirq_covered
end Leanux.Proofs.WG.Roaming.RemoteDriver.Scheduler

namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Scheduler
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open RxHistory.SchedulerSource
section
variable (entry : RemoteMap)


theorem ahead_preserves (pid : PeerId) : PrefixPreserves (Inv entry) Safe (ahead pid) :=
  cryptAhead_preserves (safe entry) _ (atoms entry) _ (encrypt_preserves entry) pid

theorem iteration_preserves (a : Activation) : PrefixPreserves (Inv entry) Safe (iteration a) :=
  RxHistory.SchedulerSource.iteration_preserves _ (atoms entry) _ _ _ _ _
    (encrypt_preserves entry) (ahead_preserves entry) (tx_preserves entry) (decrypt_preserves entry) (receiveIteration_covered entry) a

theorem run_preserves (a : Activation) : PrefixPreserves (Inv entry) Safe (run a) :=
  RxHistory.SchedulerSource.run_preserves (safe entry) (store_inv entry) _ (atoms entry) _
    (iteration_preserves entry) a

theorem dispatch_preserves (worker : Worker) : PrefixPreserves (Inv entry) Safe (dispatch worker) :=
  RxHistory.SchedulerSource.dispatch_preserves (safe entry) (store_inv entry) _ (atoms entry) _
    (run_preserves entry) worker

theorem schedule_preserves (stack : Option Worker) : PrefixPreserves (Inv entry) Safe (schedule stack) :=
  RxHistory.SchedulerSource.schedule_preserves (safe entry) (store_inv entry) _ (atoms entry) _ _ _
    (dispatch_preserves entry) (run_preserves entry) (napi_preserves entry) stack

theorem nested_preserves (worker : Worker) : PrefixPreserves (Inv entry) Safe (nested worker) :=
  RxHistory.SchedulerSource.nested_preserves (safe entry) (store_inv entry) _
    (schedule_preserves entry) worker
end
end Leanux.Proofs.WG.Roaming.RemoteDriver.Scheduler
