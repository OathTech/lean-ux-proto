import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalModel
import Leanux.Proofs.WG.TimerDiscipline.GuardedArmingClaims

/-! Projected consequences at the actual derived-hook exit. A successful session label remains separate from the wheel enqueue stamp. Stopped hook receipts have no successor; the exact pair link and live entry still hold. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

def WheelDelta (entry final : Campaign2.State) (pid : PeerId) (p : Peer) : Prop :=
  ∃ q, (final.device.bind fun d=>d.peers[pid]?)=some q ∧ q.internalId=p.internalId ∧
    q.timer .zeroKeyMaterial≠none ∧
    (∀ t,t≠.zeroKeyMaterial→q.timer t=p.timer t ∧ q.wheel t=p.wheel t) ∧
    ((final.timerEnqueues=entry.timerEnqueues ∧ q.wheel .zeroKeyMaterial=p.wheel .zeroKeyMaterial) ∨
      ∃ we, final.timerEnqueues=entry.timerEnqueues+1 ∧ q.wheel .zeroKeyMaterial=some we ∧
        we.enqueued=final.timerEnqueues)

def OtherPeers (entry final : Campaign2.State) (pid : PeerId) : Prop :=
  ∀ other,other≠pid→
    (final.device.bind fun d=>d.peers[other]?)=(entry.device.bind fun d=>d.peers[other]?)

def SessionWheelFacts (s : SessionReceipt) (r : HookJournal.Receipt) : Prop :=
  SessionDerivedLink s r ∧
  ∃ d p, r.before.wg.device=some d ∧ d.peers[r.pid]?=some p ∧ p.isDead=false ∧
    match r.outcome with
    | .error _ => True
    | .ok ((),after) =>
      after.wg.keypairCounter=s.before.wg.keypairCounter+1 ∧
      if d.running then
        peerTimerArmEffect r.before r.pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS after.wg ∧
        WheelDelta r.before.wg after.wg r.pid p ∧ OtherPeers r.before.wg after.wg r.pid
      else after.wg=r.before.wg

def WheelHistoryFacts (h : List Event) : Prop :=
  ∀ r : HookJournal.Receipt,r.hook=.sessionDerived→Event.hook r∈h→
    ∃ before s after,h=before++[.session s,.hook r]++after ∧ SessionWheelFacts s r

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
