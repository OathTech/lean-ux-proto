import Leanux.Proofs.WG.Index.StagingIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.StagingRich
open Leanux Leanux.WG

theorem sendStaged_index (pid : PeerId) :
    Campaign2.Ensures (sendStagedPackets pid) View.StagedIndexReady (fun _ => View.IndexCore) := by
  intro g a r f b pre run
  exact staged_core pid g a r f b ((ready_native g a).mp pre) run

theorem sendKeepalive_index (pid : PeerId) :
    Campaign2.Ensures (sendKeepalive pid) View.StagedIndexReady (fun _ => View.IndexCore) := by
  intro g a r f b pre run
  exact keepalive_core pid g a r f b ((ready_native g a).mp pre) run

end Leanux.Proofs.WG.Index.StagingRich
