import Leanux.Proofs.WG.Roaming.RemoteChronologyRunnerFrames
import Leanux.Proofs.WG.Roaming.RemoteChronologySyscallSource
import Leanux.Proofs.WG.Roaming.RemoteDriverRunnerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

namespace Runner
theorem normal (trace : Leanux.Runner.Trace) (placeholders : Bool) (result : Lean.Json)
    (w : World) (h : List RemoteDriver.Event)
    (run : runPrefixOuter (RemoteDriver.Runner.observed trace placeholders) [] = (.ok (result,w),h)) :
    Inv RemoteDriver.Runner.emptyRemotes h w :=
  RunnerInvariant.Normal.executeTraceWith_normal (Inv RemoteDriver.Runner.emptyRemotes) RemoteDriver.Safe
    (safe RemoteDriver.Runner.emptyRemotes) (wg_store_inv RemoteDriver.Runner.emptyRemotes)
    RemoteDriver.Syscalls.call (Syscalls.call_preserves RemoteDriver.Runner.emptyRemotes)
    trace placeholders (initial trace) run
end Runner

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
