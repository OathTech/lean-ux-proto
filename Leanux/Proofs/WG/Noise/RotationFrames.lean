import Leanux.Proofs.WG.Noise.RotationModel
import Leanux.Proofs.WG.Noise.ClearFrames

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Slot writes leave the release-readiness budget's key store unchanged. -/
theorem rotationWrite_ready (d : Device) (pid : PeerId) (change : RotationWrite)
    (p : Peer) (keys : List (Option KeypairId)) (ready : ClearReady d keys) :
    ClearReady (rotationWriteDevice d pid change p) keys := ready

end Leanux.Proofs.WG.Noise
