import Leanux.Proofs.WG.Config.LiveRemovalModel
import Leanux.Proofs.WG.Config.AllowedRemovalFrames
import Leanux.Proofs.WG.Noise.ClearFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

def cleanupContext (d : Device) := (d.sendWorkQueue, d.clearWorkQueue, d.numPeers)

theorem clearPut_cleanupContext {key : Option KeypairId} {d final : Device}
    (put : ClearPut key d final) : cleanupContext final = cleanupContext d := by
  cases put with
  | null => rfl
  | present d id k resident live word =>
    by_cases last : k.refcount = 1 <;>
      simp [cleanupContext, Index.releasedDevice, Index.unhashKeypair, last]

theorem clearRun_cleanupContext {pid : PeerId} {d final : Device} {slots : List ClearSlot}
    (steps : ClearRun pid d slots final) : cleanupContext final = cleanupContext d := by
  induction steps with
  | nil => rfl
  | cons d slot p middle final rest resident put tail ih =>
    rw [ih]
    simpa only [cleanupContext, clearWrite] using clearPut_cleanupContext put

theorem removalRun_keypairs {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) : final.keypairs = d.keypairs := by
  induction steps with
  | nil => rfl
  | cons d id rest n next final read step tail ih =>
    rw [ih]
    have hn := congrArg Device.keypairs (nodeRemoval_frame step)
    have hl := congrArg Device.keypairs (deleteListedNodes_withoutPeers id d d.peers.toList)
    simpa only [withoutTrie, withoutPeers] using hn.trans hl

theorem removalEffect_keypairs {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) : final.keypairs = d.keypairs := by
  cases ids with
  | nil => subst final; rfl
  | cons id rest => have h := removalRun_keypairs steps; exact h

end Leanux.Proofs.WG.Config
