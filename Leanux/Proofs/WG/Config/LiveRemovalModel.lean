import Leanux.Proofs.WG.Config.QuietModel
import Leanux.Proofs.WG.Noise.ClearModel

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Start at the actual post-clear device: this is the successful timer-cleanup, count-decrement and release effect.
Guard refusals are classified by source contracts; no extra slot writes occur. -/
def removedAfterClear (cleared : Device) (pid : PeerId) (p : Peer) : Device :=
  let timed := deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer p)
  Index.releasedPeerDevice { timed with numPeers := timed.numPeers - 1 } pid
    (deleteTimersPeer PeerTimer.all (emptyKeysPeer p))

/-- Successful ordered live-key clearing and final cleanup effect; guards may refuse. -/
def LiveRemovalEffect (pid : PeerId) (d : Device) (p : Peer) (final : Device) : Prop :=
  ∃ cleared, ClearRun pid d [.next, .previous, .current] cleared ∧
    final = removedAfterClear cleared pid p

end Leanux.Proofs.WG.Config
