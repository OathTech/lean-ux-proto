import Leanux.Proofs.WG.Roaming.RemoteDriverTrafficFrames
import Leanux.Proofs.WG.Origins.NormalRunnerInvariant

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Runner
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Configuration Origins.HistorySupport Std.Do

def emptyRemotes : RemoteMap := fun _=>none

theorem initial_remotes (net bare : Bool) : destinationAt (initialWG net bare) = emptyRemotes := by
  funext pid
  cases net <;> cases bare <;> rfl

theorem initial (trace : Trace) (w : World)
    (same : wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare)) :
    Inv emptyRemotes [] w := by
  have dev : w.wg.dev = (initialWG trace.net trace.bare).dev := congrArg WGStoreView.dev same
  have maps : destinationAt w.wg = emptyRemotes := by
    rw [← initial_remotes trace.net trace.bare]
    funext pid
    simp only [destinationAt,peerAt,dev]
  refine ⟨?_,by intro e member; cases member⟩
  change RemoteCovered emptyRemotes Cause [] (destinationAt w.wg)
  rw [maps]
  exact RemoteCovered.of_retained (RemoteRetained.refl _)

end Leanux.Proofs.WG.Roaming.RemoteDriver.Runner
