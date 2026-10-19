import Leanux.Proofs.WG.Config.GetterPeerCommandSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG
/-- Every normal return of the actual arbitrary peer command retains the getter
header/socket/selector observation, including errno returns. This is not a
peer-field frame or total-success claim. If the device is absent the observation
is none, so it makes no separate socket assertion at that boundary. -/
theorem setPeerCmd_getterMetadata (attrs : PeerAttrs) (entry : GetterMetadata) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>getterMetadataObservation s=entry)
      (fun _ s=>getterMetadataObservation s=entry) := by
  intro g ambient result final after pre run
  exact (GetterCleanup.normal_frame (GetterPeerCommand.command attrs) entry)
    g ambient result final after pre run
end Leanux.Proofs.WG.Config
