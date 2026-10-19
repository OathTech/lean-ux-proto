import Leanux.Proofs.WG.Config.GetterMetadataFrames
import Leanux.Proofs.WG.Config.GetterCleanupMacFrames
import Leanux.Proofs.WG.Config.ReplacementCompletionSource
import Leanux.Proofs.WG.Index.CreatorSource
import Leanux.Proofs.WG.Index.SenderIndexSource
import Leanux.Proofs.WG.Index.BulkRemovalSource
import Leanux.Proofs.WG.Roaming.RemoteTimerFrames
import Leanux.Proofs.WG.Config.AllowedRemovalReadbackFrames
import Leanux.Proofs.WG.Index.AllowedFrameSource
import Leanux.Proofs.WG.Config.GetterCleanupSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterCleanup
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do

/-- Projected initial-state contract; it does not promise that replacement
returns normally, or that the physical peer/key/node stores become empty. -/
theorem request_metadata_projected (d : Device) (sock : NlSock) (fixtures : FixtureDevices) :
    Campaign2.Ensures (wgSetDevice (replacePeersAttrs (byIndex d)))
      (fun s=>s.wg.device=some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.nlSock7=sock ∧ s.wg.fixtureNetDevices=fixtures)
      (fun result s=>result=0 ∧ getterMetadataObservation s=
        some (sendConfiguration (requestGeneration d),sock,fixtures)) := by
  intro w a result v b pre run
  exact request_metadata d sock fixtures w a result v b pre run

end Leanux.Proofs.WG.Config.GetterCleanup
