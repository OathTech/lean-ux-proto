import Leanux.Proofs.WG.Noise.DriverTagFlushSource
import Leanux.Proofs.WG.Queues.DecryptCarrier
import Leanux.Proofs.WG.Queues.EnvClearDispatch

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.SelectedDrain
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open Queues.RxCredits
open Noise.DriverTags.Flush

def SendKeeps (P : WGWorld → Prop) (send : PeerId → WG.M Unit) : Prop :=
  ∀ (w v : WGWorld) (d : Device) (pid : PeerId) (a b : Ambient),
    P w → w.dev = some d → pid ∈ d.sendWorkQueue →
    ((send pid).run w).run a = .ok (((),v),b) → P v

def ClearKeeps (P : WGWorld → Prop) (clear : PeerId → WG.M Unit) : Prop :=
  ∀ (w v : WGWorld) (d : Device) (pid : PeerId) (a b : Ambient),
    P w → w.dev = some d → pid ∈ d.clearWorkQueue →
    ((clear pid).run w).run a = .ok (((),v),b) → P v

end Leanux.Proofs.WG.Index.SelectedDrain
