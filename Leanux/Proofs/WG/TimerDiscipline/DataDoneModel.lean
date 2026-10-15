import Leanux.Proofs.WG.TimerDiscipline.View
import Leanux.WG.Data

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2
variable {α β : Type}

structure DataDoneItem where
  id : SkbId
  packet : DataPacket
  sent : Bool
  qualifies : Bool


structure DataDoneTimerCut (α : Type) where
  before : Snapshot
  value : Outcome α
  after : Snapshot


abbrev DataDoneTraversalCut := DataDoneTimerCut ((Nat × Bool) × Snapshot × Option UInt64)


abbrev DataDoneSentCut := DataDoneTimerCut (Bool × Snapshot × Option UInt64 × Snapshot × Nat)


structure DataDoneObservation where
  traversal : DataDoneTraversalCut
  items : List DataDoneItem
  sent : Bool
  beforeSent : Snapshot
  dataHook : Option DataDoneSentCut



/-- The traversal invocation's own guards qualify its recorded arm. -/
def DataDoneTraversalFacts (pid : PeerId) (cut : DataDoneTraversalCut) : Prop :=
  ∀ (d : Device) (p : Peer),
    cut.before.wg.device = some d → d.peers[pid]? = some p →
    p.persistentKeepaliveInterval ≠ 0 → d.running = true → p.isDead = false →
    cut.before.wg.armRecords = true →
    ∃ beforeRead caller afterRead,
      cut.value = .ok (((p.persistentKeepaliveInterval, true), beforeRead, some caller), afterRead) ∧
      cut.after.peerAt pid = some (p.setTimer .persistentKeepalive
        (some (caller + (p.persistentKeepaliveInterval * HZ).toUInt64))) ∧
      clockGap cut.after caller

/-- Hook presence does not itself imply an arm write: these are the hook's
actual entry guards and recorded-mode condition. -/
def DataDoneSentFacts (pid : PeerId) (cut : DataDoneSentCut) : Prop :=
  ∀ (d : Device) (p : Peer),
    cut.before.wg.device = some d → d.peers[pid]? = some p →
    p.timerPending .newHandshake = false → d.running = true → p.isDead = false →
    cut.before.wg.armRecords = true →
    ∃ beforeRead caller afterRead jitter afterJitter,
      cut.value = .ok ((true, beforeRead, some caller, afterRead, jitter), afterJitter) ∧
      jitter < HZ / 3 ∧
      cut.after.peerAt pid = some (p.setTimer .newHandshake
        (some (caller + (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧
      clockGap cut.after caller

/-- Ordered actual send results determine the data-sent hook. Expiry facts
refer to each hook's own after-state, before the remaining original suffix. -/
def DataDoneFacts (pid : PeerId) (items : List SkbId) (cut : DataDoneObservation) : Prop :=
  cut.items.map DataDoneItem.id = items ∧
  (∀ item ∈ cut.items,
    item.qualifies = (item.sent && !(item.packet.bytes.length == MESSAGE_DATA_LEN_0))) ∧
  cut.sent = cut.items.any
    (fun item => item.sent && !(item.packet.bytes.length == MESSAGE_DATA_LEN_0)) ∧
  cut.dataHook.isSome = cut.sent ∧
  DataDoneTraversalFacts pid cut.traversal ∧
  (∀ hook, cut.dataHook = some hook → DataDoneSentFacts pid hook)

end Leanux.Proofs.WG.TimerDiscipline
