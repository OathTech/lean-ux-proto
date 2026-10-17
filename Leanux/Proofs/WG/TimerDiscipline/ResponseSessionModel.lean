import Leanux.Proofs.WG.TimerDiscipline.DataDoneModel
import Leanux.Proofs.WG.Noise.SessionModel
import Leanux.Proofs.WG.Roaming.ResponseCallProductModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

structure ResponseSessionArm where
  caller : Campaign2.Product.Outcome (Option UInt64)
  afterArm : Campaign2.Product.Snapshot

structure ResponseSessionCut where
  beforeSession : Campaign2.Product.Snapshot
  begun : Bool
  afterSession : Campaign2.Product.Snapshot
  beforeArm : Campaign2.Product.Snapshot
  arm : Option ResponseSessionArm

structure ResponseSessionCall where
  response : Roaming.Product.ResponseCallCut
  session : ResponseSessionCut

def responseSessionEnd (cut : ResponseSessionCut) : Campaign2.Product.Snapshot :=
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
        (next.running = true → cut.beforeArm.ambient.armRecords = true →
          ∃ caller afterRead,
            arm.caller = .ok (some caller, afterRead) ∧
            recordedTimerEffect cut.beforeArm.wg pid q .zeroKeyMaterial
              ZERO_KEY_MATERIAL_TICKS caller arm.afterArm.wg)

def ResponseSessionObservation (msg : List UInt8)
    (outcome : Campaign2.Product.Outcome (Option ResponseSessionCall)) : Prop :=
  ∃ candidate afterPrefix, outcome = .ok (candidate, afterPrefix) ∧
    ∀ cut, candidate = some cut →
      Roaming.Product.ResponseCallFacts msg cut.response ∧
      ResponseSessionFacts cut.response.consumed.input.pid cut.session ∧
      responseSessionEnd cut.session = afterPrefix


end Leanux.Proofs.WG.TimerDiscipline
