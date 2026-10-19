import Leanux.Proofs.WG.TransmitSecurity.DriverReceiveProjection

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
variable {E F : Type} {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem resched_projects (ρ : E → Option F) (worker : Worker) (site : Decision) :
    ProjectsPrefix ρ id (reschedObserved worker site) (reschedObserved worker site) := by
  unfold reschedObserved
  repeat' driver_product_step ρ

theorem encryptTail_projects (h : HooksProjects ρ g a) (item : Option (List SkbId)) :
    ProjectsPrefix ρ id (encryptTailObserved g item) (encryptTailObserved a item) := by
  unfold encryptTailObserved workerIterPrefix
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head Hooks.encrypt; exact h.encrypt _)
    | (maintenance_head reschedObserved; exact resched_projects ρ _ _)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem encryptIter_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (encryptIterObserved g) (encryptIterObserved a) := by
  unfold encryptIterObserved
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head Hooks.poll; exact h.poll)
    | (maintenance_head softirqObserved; exact softirq_projects h)
    | (maintenance_head encryptTailObserved; exact encryptTail_projects h _)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem txIter_projects (h : HooksProjects ρ g a) (pid : PeerId) :
    ProjectsPrefix ρ id (txIterObserved g pid) (txIterObserved a pid) := by
  unfold txIterObserved workerIterPrefix
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head Hooks.transmit; exact h.transmit _)
    | (maintenance_head reschedObserved; exact resched_projects ρ _ _)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem decryptStep_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (decryptStepObserved g) (decryptStepObserved a) := by
  unfold decryptStepObserved RxWorkers.decryptWith
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head softirqObserved; exact softirq_projects h)
    | (maintenance_head irqExitObserved; exact irqExit_projects h)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem decryptIter_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (decryptIterObserved g) (decryptIterObserved a) := by
  unfold decryptIterObserved workerIterPrefix
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head decryptStepObserved; exact decryptStep_projects h)
    | (maintenance_head reschedObserved; exact resched_projects ρ _ _)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem receiveIter_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (receiveIterObserved g) (receiveIterObserved a) := by
  unfold receiveIterObserved workerIterPrefix
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head handshakeObserved; exact (handshake_projects h).liftWGObserver ρ id)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem cryptAhead_projects (h : HooksProjects ρ g a) (pid : PeerId) :
    ProjectsPrefix ρ id (cryptAheadObserved g pid) (cryptAheadObserved a pid) := by
  unfold cryptAheadObserved
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head encryptIterObserved; exact encryptIter_projects h)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem iteration_projects (h : HooksProjects ρ g a) (act : Activation) :
    ProjectsPrefix ρ id (iterationObserved g act) (iterationObserved a act) := by
  unfold iterationObserved
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head encryptIterObserved; exact encryptIter_projects h)
    | (maintenance_head decryptIterObserved; exact decryptIter_projects h)
    | (maintenance_head receiveIterObserved; exact receiveIter_projects h)
    | (maintenance_head txIterObserved; exact txIter_projects h _)
    | (maintenance_head cryptAheadObserved; exact cryptAhead_projects h _)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

private theorem schedulerRun (h : HooksProjects ρ g a) (act : Activation) :
    ProjectsPrefix ρ id (SourceScheduler.run (iterationObserved g) act)
      (SourceScheduler.run (iterationObserved a) act) := by
  unfold SourceScheduler.run
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head iterationObserved; exact iteration_projects h _)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

private theorem schedulerDispatch (h : HooksProjects ρ g a) (worker : Worker) :
    ProjectsPrefix ρ id (SourceScheduler.dispatch (iterationObserved g) worker)
      (SourceScheduler.dispatch (iterationObserved a) worker) := by
  unfold SourceScheduler.dispatch
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head SourceScheduler.run; exact schedulerRun h _)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem schedule_projects (h : HooksProjects ρ g a) (stack : Option Worker) :
    ProjectsPrefix ρ id (scheduleObserved g stack) (scheduleObserved a stack) := by
  unfold scheduleObserved SourceScheduler.schedule
  repeat' first
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head SourceScheduler.run; exact schedulerRun h _)
    | (maintenance_head SourceScheduler.dispatch; exact schedulerDispatch h _)
    | (maintenance_head softirqObserved; exact softirq_projects h)
    | (maintenance_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver ρ id)
    | driver_product_step ρ

end Leanux.Proofs.WG.TransmitSecurity.Driver
