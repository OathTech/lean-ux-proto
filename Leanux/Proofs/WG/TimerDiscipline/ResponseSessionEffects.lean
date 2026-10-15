import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionFrames
import Leanux.Proofs.WG.Noise.RotationEffects
import Leanux.Proofs.WG.Noise.SessionModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise

theorem sessionEffect_alive (pid : PeerId) (d : Device) (p : Peer)
    (counter finalCounter : Nat) (final : Device)
    (effect : SessionEffect pid d p counter true final finalCounter) :
    ∃ q, final.peers[pid]? = some q ∧ q.isDead = false := by
  simp only [SessionEffect, ite_true] at effect
  rcases effect with ⟨tag, alive, word, count, birth, rotated, rotation, hashed, rfl⟩
  have prepared : (sessionPrepared pid d p counter birth).peers[pid]? = some (sessionZeroPeer p) := by
    simp [sessionPrepared]
  have peer := rotationRun_peer rotation (sessionZeroPeer p) prepared
  refine ⟨_, peer, ?_⟩
  rw [rotationPeer_dead]
  exact alive

end Leanux.Proofs.WG.TimerDiscipline
