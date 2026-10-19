import Leanux.Proofs.WG.Config.GetterMetadataFrames
import Leanux.Proofs.WG.Config.GetterCleanupMacFrames
import Leanux.Proofs.WG.Config.ReplacementCompletionSource
import Leanux.Proofs.WG.Index.CreatorSource
import Leanux.Proofs.WG.Index.SenderIndexSource
import Leanux.Proofs.WG.Index.BulkRemovalSource
import Leanux.Proofs.WG.Roaming.RemoteTimerFrames
import Leanux.Proofs.WG.Config.AllowedRemovalReadbackFrames
import Leanux.Proofs.WG.Index.AllowedFrameSource
import Leanux.Proofs.WG.Config.GetterCleanupFrames
import Leanux.Proofs.WG.Config.GetterCleanupTimerFrames
import Leanux.Proofs.WG.Config.GetterCleanupWorkerFrames
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterCleanup
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do

/-- Normal original flag-only replacement retains getter metadata through
its real work drains. The only header change is the request-generation bump. -/
theorem request_metadata (d : Device) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (wgSetDevice (replacePeersAttrs (byIndex d)))
      (fun w=>w.dev=some d ∧ selectsDevice w d ∧
        w.nlSock7=sock ∧ w.fixtureNetDevices=fixtures)
      (fun result v=>result=0 ∧ getterMetadata v=
        some (sendConfiguration (requestGeneration d),sock,fixtures)) := by
  intro w a result v b pre run
  rw [ReplaceCompletion.native_source,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨selected,entry,c,front,tail⟩ := run
  obtain ⟨rfl,rfl⟩ := ReplaceCompletion.prefix_state d w a selected entry c
    ⟨pre.1,pre.2.1⟩ front
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨u,removed,time,removal,finish⟩ := tail
  cases u
  have metadata := (ProjectedAction.iff_run_ambient _ _ _).mp remove_all
    (ReplaceCompletion.generated w) c () removed time removal
  change ((do
    _ ← branch .setDevHasPrivateKey false
    _ ← branch .setDevHasPeers false
    _ ← branch .setDevZeroKey false
    pure (0 : Int) : WG.M Int).run removed).run time = _ at finish
  simp only [branch,AmbientM.branch] at finish
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := finish
  refine ⟨rfl,?_⟩
  rw [metadata]
  simp only [getterMetadata,ReplaceCompletion.generated,pre.1,Option.map_some,pre.2.2.1,pre.2.2.2]

end Leanux.Proofs.WG.Config.GetterCleanup
