import Leanux.Proofs.WG.Index.TimerCoreSource
import Leanux.Proofs.WG.Index.TransmitCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TimerCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem product_store {α : Type} (action : Leanux.M α) (same : SameProductStore action) :
    Preserves (fun w : World=>Ready w.wg) action :=
  by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v pre run
    exact TransmitCore.ready_product_store
      ((ProjectedAction.iff_run _ _ _).mp same w x v run) pre

end Leanux.Proofs.WG.Index.TimerCore
