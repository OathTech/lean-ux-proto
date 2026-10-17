import Leanux.Proofs.WG.TimerDiscipline.Model
import Leanux.Proofs.WG.Campaign2.ProductView

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Dequeue removes one occurrence and retains pending status for a remaining instance. -/
def dequeuedSendDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  { d with sendWorkQueue := d.sendWorkQueue.erase pid
           peers := d.peers.insert pid { p with handshakePending := (d.sendWorkQueue.erase pid).contains pid } }

/-- Every resident queued peer has reference count greater than one. -/
def RetainedSendQueue (d : Device) : Prop :=
  ∀ pid ∈ d.sendWorkQueue, ∀ p, d.peers[pid]? = some p → 1 < p.refcount

/-- The first matching association is authoritative; absent identities use the head. -/
def SendSelectionMatches (d : Device) (units : List (Nat × Nat × Nat))
    (named : Option Nat) (pid : PeerId) : Prop :=
  pid ∈ d.sendWorkQueue ∧ match named with
  | none => d.sendWorkQueue.head? = some pid
  | some address => ∃ entry,
      units.find? (fun e => e.1 == address && e.2.1 == Worker.sendWorker.index) = some entry ∧
      entry.2.2 = pid

/-- Observations at the actual ordered points of an original send-worker execution. -/
structure SendWorkerExecution where
  named : Option Nat
  pid : PeerId
  beforeSection : Campaign2.Product.Snapshot
  startBytes : List UInt8
  afterStart : Campaign2.Product.Snapshot
  afterBody : Campaign2.Product.Snapshot
  stopBytes : List UInt8

/-- Selection/dequeue facts and the retained worker outcome at actual section points. -/
def CompletedSendWorker (d : Device) (units : List (Nat × Nat × Nat))
    (execution : SendWorkerExecution) (final : Campaign2.Product.Snapshot) : Prop :=
  SendSelectionMatches d units execution.named execution.pid ∧
  ∃ p, d.peers[execution.pid]? = some p ∧ p.handshakePending = true ∧
    execution.beforeSection.wg.device = some (dequeuedSendDevice d execution.pid p) ∧
    execution.afterStart.wg.device = some (dequeuedSendDevice d execution.pid p) ∧
    workerObservation execution.afterBody.toSnapshot execution.pid =
      some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1) ∧
    workerObservation final.toSnapshot execution.pid =
      some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1)

end Leanux.Proofs.WG.TimerDiscipline
