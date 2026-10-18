import Leanux.Proofs.WG.Index.ReachedSchedulerModel
import Leanux.Proofs.WG.Index.ReachedProjectionFrames
import Leanux.Proofs.WG.Index.ReceiverCoreBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Queues Queues.RxCredits

theorem schedulerInput_snapshot (initial : Ledger) (loans : Reservations)
    (before history : List RxHistory.Event) (w : World) :
    View.SchedulerInput initial loans before history (Campaign2.snapshot w.wg w.ambient) ↔
      Reached.Aux initial loans before history w := by
  constructor
  · rintro ⟨v,same,pre⟩
    exact Reached.aux_wg_equal (receiveInput_world (congrArg Campaign2.Snapshot.wg same)) pre
  · intro pre
    exact ⟨w,rfl,pre⟩

end Leanux.Proofs.WG.Index
