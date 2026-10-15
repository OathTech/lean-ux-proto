import Leanux.Proofs.WG.TimerDiscipline.DataDoneModel
import Leanux.WG.RxData

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The actual traversal and optional data-received invocations, before the
remaining inner-packet validation and routing. A hook need not write a timer. -/
structure RxDataTimersCut where
  traversal : DataDoneTraversalCut
  dataReceived : Option (DataDoneTimerCut ((Option Bool × Snapshot × Option UInt64)))
  keepalive : Bool

/-- The existing receipt rule, evaluated at the hook's actual entry and exit. -/
def RxDataReceiptEffect (pid : PeerId) (d : Device) (p : Peer) (after : Snapshot) : Prop :=
  if d.running then
    if p.timerPending .sendKeepalive then
      after.peerAt pid = some { p with timerNeedAnotherKeepalive := true }
    else if p.isDead then after.peerAt pid = some p
    else ∃ expiry, after.peerAt pid = some (p.setTimer .sendKeepalive (some expiry))
  else after.peerAt pid = some p

def RxDataReceiptFacts (pid : PeerId)
    (cut : DataDoneTimerCut (Option Bool × Snapshot × Option UInt64)) : Prop :=
  (∀ (d : Device) (p : Peer), cut.before.wg.device = some d →
    d.peers[pid]? = some p → RxDataReceiptEffect pid d p cut.after) ∧
  (∀ (d : Device) (p : Peer), cut.before.wg.device = some d →
    d.peers[pid]? = some p → p.timerPending .sendKeepalive = false →
    d.running = true → p.isDead = false → cut.before.wg.armRecords = true →
    ∃ beforeRead caller afterRead,
      cut.value = .ok ((some true, beforeRead, some caller), afterRead) ∧
      cut.after.peerAt pid = some (p.setTimer .sendKeepalive
        (some (caller + KEEPALIVE_TIMEOUT_TICKS.toUInt64))) ∧ clockGap cut.after caller)

/-- Raw packet scope: no authentication or inner-packet acceptance is inferred. -/
def RxDataTimersFacts (pid : PeerId) (pkt : RxPacket) (cut : RxDataTimersCut) : Prop :=
  cut.keepalive = (pkt.bytes.length == 0) ∧
  cut.dataReceived.isSome = !cut.keepalive ∧
  DataDoneTraversalFacts pid cut.traversal ∧
  (∀ receipt, cut.dataReceived = some receipt → RxDataReceiptFacts pid receipt)

end Leanux.Proofs.WG.TimerDiscipline
