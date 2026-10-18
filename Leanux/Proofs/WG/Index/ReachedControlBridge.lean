import Leanux.Proofs.WG.Index.LifecycleEnvironmentSource
import Leanux.Proofs.WG.Index.ReachedRunnerSource
import Leanux.Proofs.WG.Noise.DriverTagRetainedSource
import Leanux.Proofs.WG.Index.DumpDispatchSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedControls
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem entry_configuration {cs : Ledger} {loans : Reservations}
    {h : List RxHistory.Event} {w : World} (pre : Reached.Entry cs loans h w) :
    ConfigurationIndex.Entry cs loans w.wg :=
  ⟨pre.1.1.1,pre.1.1.2.2,pre.2⟩

end Leanux.Proofs.WG.Index.ReachedControls
