import Leanux.Proofs.WG.TimerDiscipline.DataDoneModel
import Leanux.Proofs.WG.TimerDiscipline.GuardedArmingClaims
import Leanux.WG.RxData

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

/-- The actual traversal and optional data-received invocations, before the
remaining inner-packet validation and routing. A hook need not write a timer. -/
structure RxDataTimersCut where
  traversal : DataDoneTraversalCut
  dataReceived : Option (DataDoneTimerCut ((Option Bool × Product.Snapshot × Option UInt64)))
  keepalive : Bool

/-- The existing receipt rule, evaluated at the hook's actual entry and exit. -/
def RxDataReceiptEffect (pid : PeerId) (d : Device) (p : Peer)
    (before after : Product.Snapshot) : Prop :=
  if d.running then
    if p.timerPending .sendKeepalive then
      after.wg = {before.wg with device := some {d with peers := d.peers.insert pid {p with timerNeedAnotherKeepalive := true}}}
    else if p.isDead then after.wg = before.wg
    else peerTimerArmEffect before.toSnapshot pid p .sendKeepalive KEEPALIVE_TIMEOUT_TICKS after.wg
  else after.wg = before.wg

def RxDataReceiptFacts (pid : PeerId)
    (cut : DataDoneTimerCut (Option Bool × Product.Snapshot × Option UInt64)) : Prop :=
  (∀ (d : Device) (p : Peer), cut.before.wg.device = some d →
    d.peers[pid]? = some p → RxDataReceiptEffect pid d p cut.before cut.after) ∧
  (∀ (d : Device) (p : Peer), cut.before.wg.device = some d →
    d.peers[pid]? = some p → p.timerPending .sendKeepalive = false →
    d.running = true → p.isDead = false → cut.before.ambient.armRecords = true →
    ∃ beforeRead caller afterRead,
      cut.value = .ok ((some true, beforeRead, some caller), afterRead) ∧
      recordedTimerEffect beforeRead.wg pid p .sendKeepalive KEEPALIVE_TIMEOUT_TICKS caller cut.after.wg)

/-- Raw packet scope: no authentication or inner-packet acceptance is inferred. -/
def RxDataTimersFacts (pid : PeerId) (pkt : RxPacket) (cut : RxDataTimersCut) : Prop :=
  cut.keepalive = (pkt.bytes.length == 0) ∧
  cut.dataReceived.isSome = !cut.keepalive ∧
  DataDoneTraversalFacts pid cut.traversal ∧
  (∀ receipt, cut.dataReceived = some receipt → RxDataReceiptFacts pid receipt)


end Leanux.Proofs.WG.TimerDiscipline
