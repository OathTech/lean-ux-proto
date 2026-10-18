import Leanux.Proofs.WG.Index.ReachedSchedulerSource
import Leanux.Proofs.WG.Index.TimerProductCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem encrypt_iteration_index  :
    Campaign2.Product.Ensures (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker))
      (fun s=>View.StagedIndexReady s.toSnapshot) (fun _ s=>View.StagedIndexReady s.toSnapshot) := by
  intro w result v pre run
  exact (StagingRich.ready_native v.wg v.ambient).mpr
    ((hoare_iff_run _ _ _).mp (EncryptCore.original_ready PollCore.softirq_ready) w result v
      ((StagingRich.ready_native w.wg w.ambient).mp pre) run)

theorem timer_dispatch_index (worker : Worker) (pid : PeerId) (timer : PeerTimer) (wheel : WheelEntry) (prior : Option UInt64) :
    Campaign2.Product.Ensures (timerDispatchUnit worker pid timer wheel prior)
      (fun s=>View.StagedIndexReady s.toSnapshot) (fun _ s=>View.StagedIndexReady s.toSnapshot) := by
  intro w result v pre run
  exact (StagingRich.ready_native v.wg v.ambient).mpr
    ((hoare_iff_run _ _ _).mp (TimerCore.dispatch_ready worker pid timer wheel prior) w result v
      ((StagingRich.ready_native w.wg w.ambient).mp pre) run)

theorem timer_placeholder_index (j : UInt64) :
    Campaign2.Product.Ensures (RxHistory.placeholderTimerPassSource j)
      (fun s=>View.StagedIndexReady s.toSnapshot) (fun _ s=>View.StagedIndexReady s.toSnapshot) := by
  intro w result v pre run
  exact (StagingRich.ready_native v.wg v.ambient).mpr
    ((hoare_iff_run _ _ _).mp (TimerCore.placeholder_ready j) w result v
      ((StagingRich.ready_native w.wg w.ambient).mp pre) run)

end Leanux.Proofs.WG.Index
