import Leanux.Env
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Exactly the bounded recorded turns of `afterBatch`, including its original
peek and queue test. No successful scheduling premise is built into this action. -/
def afterBatchRecordedLoop : Leanux.M Unit := do
  for _ in [0:(← recordBudget)] do
    schedule
    if (← peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← getDev).sendWorkQueue.isEmpty then
      runOneSendWorker
    else break

def afterBatchDrainSuffix : Leanux.M Unit := do
  let d ← getDev
  requireDrained "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0]
  deliverSent

def afterBatchRecorded : Leanux.M Unit := do
  modifyWG fun w => {w with queuedThisCall := []}
  afterBatchRecordedLoop
  afterBatchDrainSuffix

/-- The six explicit completion checks and NAPI guard, at a present device. -/
def BatchDrained (s : Campaign2.Product.Snapshot) : Prop :=
  ∃ d, s.wg.device = some d ∧ d.decryptQueue.empty = true ∧
    d.encryptQueue.empty = true ∧ d.txWorkQueue.isEmpty = true ∧
    d.sendWorkQueue.isEmpty = true ∧ d.handshakeQueue.empty = true ∧
    d.handshakeQueueLen = 0 ∧ d.peers.toList.any (·.2.napiScheduled) = false

end Leanux.Proofs.WG.Progress
