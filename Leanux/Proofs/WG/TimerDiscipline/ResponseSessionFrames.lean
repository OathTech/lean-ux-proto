import Leanux.Proofs.WG.Noise.RotationModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise

theorem rotationPeer_dead (actions : List RotationAction) (p : Peer) :
    (rotationPeer actions p).isDead = p.isDead := by
  induction actions generalizing p with
  | nil => rfl
  | cons action rest ih =>
    cases action with
    | put key => exact ih p
    | write change =>
      change (rotationPeer rest (change.apply p)).isDead = _
      rw [ih]
      cases change <;> rfl

end Leanux.Proofs.WG.TimerDiscipline
