import Leanux.Proofs.WG.Index.CryptCutSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.EncryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem product_core_store {α : Type} (action : Leanux.M α) (same : SameProductStore action) :
    Preserves (fun w : World=>Reached.Core w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  exact Reached.core_device
    (congrArg (fun s : ProductStore43=>s.2.2.2.dev)
      ((ProjectedAction.iff_run _ _ _).mp same w result v run)) pre

end Leanux.Proofs.WG.Index.EncryptCore
