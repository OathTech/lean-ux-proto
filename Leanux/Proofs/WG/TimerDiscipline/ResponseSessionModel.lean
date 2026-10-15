import Leanux.Proofs.WG.TimerDiscipline.View
import Leanux.Proofs.WG.Noise.SessionModel
import Leanux.Proofs.WG.Roaming.ResponseModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming

structure ResponseSessionArm where
  caller : Outcome (Option UInt64)
  afterArm : Snapshot

structure ResponseSessionCut where
  beforeSession : Snapshot
  begun : Bool
  afterSession : Snapshot
  beforeArm : Snapshot
  arm : Option ResponseSessionArm

structure ResponseSessionCall where
  response : ResponseCallCut
  session : ResponseSessionCut

def responseSessionEnd (cut : ResponseSessionCut) : Snapshot :=
  match cut.arm with
  | none => cut.beforeArm
  | some arm => arm.afterArm

def ResponseSessionFacts (pid : PeerId) (cut : ResponseSessionCut) : Prop :=
  ∃ d p next,
    cut.beforeSession.wg.device = some d ∧ d.peers[pid]? = some p ∧
    cut.afterSession.wg.device = some next ∧
    SessionEffect pid d p cut.beforeSession.wg.keypairCounter cut.begun next
      cut.afterSession.wg.keypairCounter ∧
    cut.beforeArm.wg.device = some next ∧
    cut.beforeArm.wg.keypairCounter = cut.afterSession.wg.keypairCounter ∧
    cut.arm.isSome = cut.begun ∧
    ∀ arm, cut.arm = some arm →
      cut.beforeArm.wg.keypairCounter = cut.beforeSession.wg.keypairCounter + 1 ∧
      ∃ q, next.peers[pid]? = some q ∧ q.isDead = false ∧
        (next.running = true → cut.beforeArm.wg.armRecords = true →
          ∃ caller afterRead,
            arm.caller = .ok (some caller, afterRead) ∧
            arm.afterArm.peerAt pid = some (q.setTimer .zeroKeyMaterial
              (some (caller + ZERO_KEY_MATERIAL_TICKS.toUInt64))) ∧
            clockGap arm.afterArm caller)

def ResponseSessionObservation (msg : List UInt8)
    (outcome : Outcome (Option ResponseSessionCall)) : Prop :=
  ∃ candidate afterPrefix, outcome = .ok (candidate, afterPrefix) ∧
    ∀ cut, candidate = some cut →
      ResponseCallFacts msg cut.response ∧
      ResponseSessionFacts cut.response.consumed.input.pid cut.session ∧
      responseSessionEnd cut.session = afterPrefix

end Leanux.Proofs.WG.TimerDiscipline
