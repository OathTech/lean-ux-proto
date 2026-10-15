import Leanux.Proofs.WG.TimerDiscipline.Model

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The original dequeue removes one occurrence and clears the selected flag. -/
def dequeuedSendDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  { d with sendWorkQueue := d.sendWorkQueue.erase pid
           peers := d.peers.insert pid { p with handshakePending := false } }

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
  beforeSection : Snapshot
  startBytes : List UInt8
  afterStart : Snapshot
  afterBody : Snapshot
  stopBytes : List UInt8

/-- Selection/dequeue facts and the retained worker outcome at actual section points. -/
def CompletedSendWorker (d : Device) (units : List (Nat × Nat × Nat))
    (execution : SendWorkerExecution) (final : Snapshot) : Prop :=
  SendSelectionMatches d units execution.named execution.pid ∧
  ∃ p, d.peers[execution.pid]? = some p ∧ p.handshakePending = true ∧
    execution.beforeSection.wg.device = some (dequeuedSendDevice d execution.pid p) ∧
    execution.afterStart.wg.device = some (dequeuedSendDevice d execution.pid p) ∧
    workerObservation execution.afterBody execution.pid =
      some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1) ∧
    workerObservation final execution.pid =
      some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1)

end Leanux.Proofs.WG.TimerDiscipline
