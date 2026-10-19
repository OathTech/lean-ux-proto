import Leanux.Proofs.WG.Config.PeerScalarRetentionFrames
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.PeerScalarRetention
open Leanux Leanux.WG Noise Std.Do

theorem staged (pid : PeerId) (initial : Map) :
    Campaign2.Ensures (sendStagedPackets pid)
      (fun s=>observation s=initial)
      (fun _ s=>Retained initial (observation s)) := by
  intro g a result final b pre run
  exact pre ▸ frame_retained
    (Index.StagingRich.sendStagedPackets_rich pid g g a result final b
      (Index.StagingRich.refl g) run)

theorem keepalive (pid : PeerId) (initial : Map) :
    Campaign2.Ensures (sendKeepalive pid)
      (fun s=>observation s=initial)
      (fun _ s=>Retained initial (observation s)) := by
  intro g a result final b pre run
  exact pre ▸ frame_retained
    (Index.StagingRich.sendKeepalive_rich pid g g a result final b
      (Index.StagingRich.refl g) run)

end Leanux.Proofs.WG.Config.PeerScalarRetention
