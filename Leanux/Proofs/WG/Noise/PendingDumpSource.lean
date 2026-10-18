import Leanux.Proofs.WG.Noise.PendingDumpFrames
import Leanux.Proofs.WG.Noise.PendingControlSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingDump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do PendingSession

/-- The original full and stepped dump family preserves the pending invariant on
every normal return. Cursors may be present, dead, or released during the call. -/
theorem native (action : NetlinkDumpCall) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) action.original :=
  Config.DumpInvariant.call (contracts seen) action

/-- The existing actual lifetime observer, including its Stop behavior, adds no
confirmation labels and preserves the pending-session history invariant. -/
theorem observed (action : NetlinkDumpCall) :
    PrefixPreserves StateInv HistorySafe
      (RxHistory.mixed (liftWGObserver action.observed)) :=
  lifecycle_observed action.observed action.original action.erases (native action)

end Leanux.Proofs.WG.Noise.PendingDump
