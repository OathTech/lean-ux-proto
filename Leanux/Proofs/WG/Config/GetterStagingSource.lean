import Leanux.Proofs.WG.Config.GetterStagingFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterStaging
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open GetterCleanup

theorem staged (pid : PeerId) : SameView getterMetadata (sendStagedPackets pid) :=
  fun initial=>(ensures_iff _ _ _).mp
    (Index.StagingPreservation.sendStagedPackets_rule pid (contracts initial))
theorem keepalive (pid : PeerId) : SameView getterMetadata (sendKeepalive pid) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  apply Index.StagingRich.keepalive_rule pid _ _ (fun _ h=>h)
    (normal_frame (staged pid) initial)
  intro g d p mtu hd hp pre
  simpa only [getterMetadata,hd,Option.map_some,sendConfiguration] using pre
end Leanux.Proofs.WG.Config.GetterStaging
