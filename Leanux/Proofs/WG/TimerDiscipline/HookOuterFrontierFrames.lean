import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierBridge
import Leanux.Proofs.Framing.Product
/-! The filesystem lift leaves the WireGuard allocation counter unchanged by its type. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing HandshakeJournal

theorem files_frontier {α : Type} (action : FS.M α) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (liftPrefix (liftFS action)) :=
  quiet_frontier _ (product_snapshot_counter
    (fun initial=>productFS_spec action (fun w=>Keypairs.snapshot w.wg=initial)
      (fun _ _ _ _ pre=>pre)))

end Leanux.Proofs.WG.TimerDiscipline.HookCommon

