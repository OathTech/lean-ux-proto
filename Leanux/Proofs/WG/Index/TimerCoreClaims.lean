import Leanux.Proofs.WG.Index.TimerCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TimerCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem callback_index (pid : PeerId) (timer : PeerTimer) :
    Campaign2.Ensures (timerCallback pid timer) View.StagedIndexReady
      (fun _ => View.StagedIndexReady) := by
  intro w a result v b pre run
  exact (StagingRich.ready_native v b).mpr
    (callback pid timer w a result v b ((StagingRich.ready_native w a).mp pre) run)

end Leanux.Proofs.WG.Index.TimerCore
