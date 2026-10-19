import Leanux.Proofs.WG.Roaming.RemoteChronologyCaptureSource
import Leanux.Proofs.WG.Roaming.RemoteDriverRunnerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

namespace Runner
theorem initial (trace : Leanux.Runner.Trace) (w : World)
    (same : wgStoreView w.wg = wgStoreView (Leanux.Runner.initialWG trace.net trace.bare)) :
    Inv RemoteDriver.Runner.emptyRemotes [] w := by
  have inherited := RemoteDriver.Runner.initial trace w same
  refine ⟨?_,inherited.2⟩
  apply nil_of_retained
  intro pid remote present
  rcases inherited.1 pid remote present with earlier | ⟨event,member,_⟩
  · exact earlier
  · cases member

end Runner

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
