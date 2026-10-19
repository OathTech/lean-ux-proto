import Leanux.Proofs.WG.Config.ConfiguredBoundaryModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- Configuration ownership across device absence. A present device carries
the exact represented ownership boundary used by the native command proofs. -/
def OptionalReady (g : WGWorld) : Prop :=
  ∀ d, g.dev = some d → DeviceReady d

def ProjectedOptionalReady (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → DeviceReady d


end Leanux.Proofs.WG.Config.OwnerConfiguration
