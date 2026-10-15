import Leanux.Proofs.WG.Noise.RotationFrames
import Leanux.Proofs.WG.Noise.ClearEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem rotationRun_peer {pid : PeerId} {d final : Device} {actions : List RotationAction}
    (steps : RotationRun pid d actions final) (p : Peer) (resident : d.peers[pid]? = some p) :
    final.peers[pid]? = some (rotationPeer actions p) := by
  induction steps generalizing p with
  | nil => exact resident
  | write d final change q rest found tail ih =>
    rw [resident] at found
    cases found
    exact ih (change.apply q) (by simp [rotationWriteDevice])
  | put d middle final key rest release tail ih =>
    exact ih p (by rw [clearPut_peers release]; exact resident)

/-- Static readiness constructs the ordered effect, including repeated puts. -/
theorem rotationRun_exists (pid : PeerId) (d : Device) (p : Peer) (actions : List RotationAction)
    (resident : d.peers[pid]? = some p)
    (ready : ClearReady d (rotationReleases actions)) :
    ∃ final, RotationRun pid d actions final := by
  induction actions generalizing d p with
  | nil => exact ⟨d, .nil d⟩
  | cons action rest ih =>
    cases action with
    | write change =>
      obtain ⟨final, tail⟩ := ih (rotationWriteDevice d pid change p) (change.apply p)
        (by simp [rotationWriteDevice]) (rotationWrite_ready d pid change p _ ready)
      exact ⟨final, .write d final change p rest resident tail⟩
    | put key =>
      obtain ⟨middle, release, budget⟩ := clearPut_exists key d (rotationReleases rest) ready
      obtain ⟨final, tail⟩ := ih middle p (by rw [clearPut_peers release]; exact resident) budget
      exact ⟨final, .put d middle final key rest release tail⟩

theorem confirmationEffect_peer (pid : PeerId) (received : KeypairId) (d final : Device)
    (p : Peer) (ok : Bool) (resident : d.peers[pid]? = some p)
    (effect : ConfirmationEffect pid received d p ok final) :
    final.peers[pid]? = some (if ok then rotationPeer (confirmationPlan p received) p else p) := by
  by_cases matched : p.keypairNext = some received
  · simp only [ConfirmationEffect, matched, if_pos] at effect
    obtain ⟨rfl, steps⟩ := effect
    exact rotationRun_peer steps p resident
  · simp only [ConfirmationEffect, matched, if_neg] at effect
    obtain ⟨rfl, rfl⟩ := effect
    exact resident

end Leanux.Proofs.WG.Noise
