import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionModel
import Leanux.Proofs.WG.TimerDiscipline.GuardedArmingClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- The serial labels the actual successful allocation event, not a promise
that its keypair survives aliased rotation. Hook presence is exactly `begun`.
The running guard distinguishes the logical arm from its possible wheel enqueue. -/
def SessionArmEvent (pid : PeerId) (cut : ResponseSessionCut) : Prop :=
  ResponseSessionFacts pid cut ∧
  ∀ arm, cut.arm = some arm → ∃ d p,
    cut.beforeArm.wg.device = some d ∧ d.peers[pid]? = some p ∧ p.isDead = false ∧
    arm.afterArm.wg.keypairCounter = cut.beforeSession.wg.keypairCounter + 1 ∧
    (if d.running then
      peerTimerArmEffect cut.beforeArm.toSnapshot pid p .zeroKeyMaterial
        ZERO_KEY_MATERIAL_TICKS arm.afterArm.wg
     else arm.afterArm.wg = cut.beforeArm.wg) ∧
    (arm.afterArm.wg.timerEnqueues = cut.beforeArm.wg.timerEnqueues ∨
      arm.afterArm.wg.timerEnqueues = cut.beforeArm.wg.timerEnqueues + 1)

end Leanux.Proofs.WG.TimerDiscipline
