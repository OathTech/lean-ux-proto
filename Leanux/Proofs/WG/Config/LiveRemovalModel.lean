import Leanux.Proofs.WG.Config.QuietModel
import Leanux.Proofs.WG.Noise.ClearModel

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Start at the actual post-clear device: only timer writes, count decrement
and the final peer release remain. No additional empty-slot writes are inserted. -/
def removedAfterClear (cleared : Device) (pid : PeerId) (p : Peer) : Device :=
  let timed := deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer p)
  Index.releasedPeerDevice { timed with numPeers := timed.numPeers - 1 } pid
    (deleteTimersPeer PeerTimer.all (emptyKeysPeer p))

/-- Ordered live-key clearing followed by the original quiet removal suffix. -/
def LiveRemovalEffect (pid : PeerId) (d : Device) (p : Peer) (final : Device) : Prop :=
  ∃ cleared, ClearRun pid d [.next, .previous, .current] cleared ∧
    final = removedAfterClear cleared pid p

end Leanux.Proofs.WG.Config
