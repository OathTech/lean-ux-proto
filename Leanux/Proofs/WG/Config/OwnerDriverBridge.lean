import Leanux.Proofs.WG.Config.ConfiguredOptionalModel
import Leanux.Proofs.WG.Index.ReachedRunnerBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerDriver
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Config.OwnerConfiguration

def Inv (h : List RxHistory.Event) (w : World) : Prop :=
  Index.Reached.AnyEntry h w ∧ OptionalReady w.wg

theorem safe (h : List RxHistory.Event) (w : World) (pre : Inv h w) :
    OwnerChecks.Safe h := Index.Reached.anyEntry_safe h w pre.1

end Leanux.Proofs.WG.Config.OwnerDriver
