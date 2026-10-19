import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryReceive

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
variable {E : Type} {Safe : List E → Prop} {g : Hooks E}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem resched_history (worker : Worker) (site : Decision) :
    ProductHistorySafe Safe (reschedObserved worker site) := by
  unfold reschedObserved
  repeat' driver_product_history_step

theorem encryptTail_history (h : ActorHistorySafe Safe g) (item : Option (List SkbId)) :
    ProductHistorySafe Safe (encryptTailObserved g item) := by
  unfold encryptTailObserved workerIterPrefix
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head Hooks.encrypt; exact h.encrypt _)
    | (driver_history_head reschedObserved; exact resched_history _ _)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

theorem encryptIter_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (encryptIterObserved g) := by
  unfold encryptIterObserved
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head Hooks.poll; exact h.poll)
    | (driver_history_head softirqObserved; exact softirq_history h)
    | (driver_history_head encryptTailObserved; exact encryptTail_history h _)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

theorem txIter_history (h : ActorHistorySafe Safe g) (pid : PeerId) :
    ProductHistorySafe Safe (txIterObserved g pid) := by
  unfold txIterObserved workerIterPrefix
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head Hooks.transmit; exact h.transmit _)
    | (driver_history_head reschedObserved; exact resched_history _ _)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

theorem decryptStep_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (decryptStepObserved g) := by
  unfold decryptStepObserved RxWorkers.decryptWith
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head softirqObserved; exact softirq_history h)
    | (driver_history_head irqExitObserved; exact irqExit_history h)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

theorem decryptIter_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (decryptIterObserved g) := by
  unfold decryptIterObserved workerIterPrefix
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head decryptStepObserved; exact decryptStep_history h)
    | (driver_history_head reschedObserved; exact resched_history _ _)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

theorem receiveIter_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (receiveIterObserved g) := by
  unfold receiveIterObserved workerIterPrefix
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head handshakeObserved; exact (handshake_history h).liftWGObserver)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

theorem cryptAhead_history (h : ActorHistorySafe Safe g) (pid : PeerId) :
    ProductHistorySafe Safe (cryptAheadObserved g pid) := by
  unfold cryptAheadObserved
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head encryptIterObserved; exact encryptIter_history h)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

theorem iteration_history (h : ActorHistorySafe Safe g) (act : Activation) :
    ProductHistorySafe Safe (iterationObserved g act) := by
  unfold iterationObserved
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head encryptIterObserved; exact encryptIter_history h)
    | (driver_history_head decryptIterObserved; exact decryptIter_history h)
    | (driver_history_head receiveIterObserved; exact receiveIter_history h)
    | (driver_history_head txIterObserved; exact txIter_history h _)
    | (driver_history_head cryptAheadObserved; exact cryptAhead_history h _)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

private theorem schedulerRun (h : ActorHistorySafe Safe g) (act : Activation) :
    ProductHistorySafe Safe (SourceScheduler.run (iterationObserved g) act) := by
  unfold SourceScheduler.run
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head iterationObserved; exact iteration_history h _)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

private theorem schedulerDispatch (h : ActorHistorySafe Safe g) (worker : Worker) :
    ProductHistorySafe Safe (SourceScheduler.dispatch (iterationObserved g) worker) := by
  unfold SourceScheduler.dispatch
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head SourceScheduler.run; exact schedulerRun h _)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

theorem schedule_history (h : ActorHistorySafe Safe g) (stack : Option Worker) :
    ProductHistorySafe Safe (scheduleObserved g stack) := by
  unfold scheduleObserved SourceScheduler.schedule
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head SourceScheduler.run; exact schedulerRun h _)
    | (driver_history_head SourceScheduler.dispatch; exact schedulerDispatch h _)
    | (driver_history_head softirqObserved; exact softirq_history h)
    | (driver_history_head Hooks.peerRelease; exact (h.peerRelease _).liftWGObserver)
    | driver_product_history_step

end Leanux.Proofs.WG.TransmitSecurity.Driver
