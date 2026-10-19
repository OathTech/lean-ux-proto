import Leanux.Proofs.WG.Noise.DriverTagRemovalFactors
import Leanux.Proofs.WG.Noise.DriverTagFlushCallerSource
import Leanux.Proofs.WG.Noise.DriverTagAllowedFrames
import Leanux.Proofs.WG.Queues.JointRemoval
import Leanux.Proofs.WG.Queues.JointDestruct

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Removal
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Configuration
universe u

/-! Physical tag frames. The removal retains tags until an actual helper
changes one or administrative release deletes its peer. -/
theorem makeDead_tags (pid : PeerId) : SameView tagView (WG.peerMakeDead pid) := by
  rw [Configuration.peerMakeDead_factor]
  unfold Configuration.peerMakeDeadWith
  exact (modifyDev_frame (fun d => {d with peerList := d.peerList.filter (· != pid)}) (fun _ => rfl)).bind (fun _ =>
    (removeByPeer_frame pid).bind (fun _ =>
    (store_frame getDev_sameWGStore).bind (fun d =>
    (ambient_frame (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid)))).bind (fun _ =>
    (modifyDev_frame (fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}) (fun _ => rfl)).bind (fun _ =>
      modifyPeer_frame pid (fun p => {p with isDead := true}) (fun _ => rfl))))))

theorem destructFinish_retains (g : WGWorld) (ambient : Ambient) (result : Unit)
    (final : WGWorld) (after : Ambient)
    (run : (destructFinishSource.run g).run ambient = .ok ((result,final),after)) :
    TagsRetained (responseTagMap g.dev) (responseTagMap final.dev) := by
  cases result
  have gone := (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish_none)
    g final ambient after run
  have absent : final.dev = none := by
    simpa only [AllowedIps.routingView,Option.map_eq_none_iff] using gone
  intro pid tag present
  simp [responseTagMap,absent] at present

end Leanux.Proofs.WG.Noise.DriverTags.Removal
