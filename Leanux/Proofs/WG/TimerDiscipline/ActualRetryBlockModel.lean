import Leanux.Proofs.WG.TimerDiscipline.OuterAdjacentModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- Two consecutive actual turn receipts, first retransmit then send. -/
abbrev ActualRetryPair := OuterTimerTurnReceipt × OuterTimerTurnReceipt

/-- The observed branch conditions required by the checked adjacent-pair
certificate. No certificate, successful intermediate execution or entry
readiness is assumed here. -/
def ActualRetryPairMatches (jPass : UInt64) (pid : PeerId) (pair : ActualRetryPair) : Prop :=
  ∃ d after we,
    pair.1.before.wg.device = some d ∧ d.sendWorkQueue = [] ∧
    outerTimerChoice jPass pair.1.before = some ⟨.timerRetransmit,pid,.retransmitHandshake,we⟩ ∧
    (pair.2.before.ambient.hidden.bind fun rs =>
      (rs.find? fun r => !HiddenSite.passive r.site).map (·.site)) =
        some (HiddenSite.sectionStart .sendWorker).info.id ∧
    pair.2.before.wg.device = some after ∧ after.sendWorkQueue.isEmpty = false

/-- Preserve both receipts of every pair, in their actual order. -/
def actualRetryBlockTurns (pairs : List ActualRetryPair) : List OuterTimerTurnReceipt :=
  pairs.flatMap fun pair => [pair.1,pair.2]

/-- Last send exit of a nonempty block; later episode turns are excluded. -/
def actualRetryBlockExit (first : ActualRetryPair) : List ActualRetryPair → Campaign2.Product.Snapshot
  | [] => first.2.after
  | next :: rest => actualRetryBlockExit next rest

/-- The conclusion is at the block's last actual send exit. Later turns and
final delivery are outside its scope. The block is nonempty by construction.
The source constant `MAX_TIMER_HANDSHAKES + 1` is 19. -/
def ActualRetryBlockEffect (pid : PeerId) (first : ActualRetryPair) (rest : List ActualRetryPair) : Prop :=
  ∃ before after,
    first.1.before.toSnapshot.peerAt pid = some before ∧
    (actualRetryBlockExit first rest).toSnapshot.peerAt pid = some after ∧
    after.internalId = before.internalId ∧
    after.timerHandshakeAttempts = before.timerHandshakeAttempts + (rest.length + 1) ∧
    after.refcount = before.refcount ∧ after.handshakePending = false ∧
    after.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES + 1 ∧
    (actualRetryBlockExit first rest).wg.device.map Device.sendWorkQueue = some []

end Leanux.Proofs.WG.TimerDiscipline
