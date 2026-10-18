import Leanux.Proofs.WG.Roaming.RemoteDriverSyscallSource
import Leanux.Proofs.WG.Roaming.RemoteProvenanceSource
import Leanux.Proofs.WG.Origins.NormalRunnerInvariant
import Leanux.Proofs.WG.Queues.JointRunner
import Leanux.Proofs.WG.Noise.DriverTagRunnerSource

import Leanux.Proofs.WG.Roaming.RemoteDriverRunnerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Runner
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Configuration Origins.HistorySupport Std.Do

def observed (trace : Trace) (placeholders : Bool) : PrefixOuter Event (Json × World) :=
  RoutingJoint.executeTraceWith Syscalls.call (fun j w=>(j,w)) trace placeholders

def history (trace : Trace) (placeholders : Bool) : List Event :=
  (runPrefixOuter (observed trace placeholders) []).2

end Leanux.Proofs.WG.Roaming.RemoteDriver.Runner
