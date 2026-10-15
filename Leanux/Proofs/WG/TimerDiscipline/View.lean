import Leanux.Proofs.WG.Campaign2.View

/-! Pure observations used by timer claims, independent of execution state. -/
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

abbrev RetryView := Nat × Nat × Option UInt64
def retryView (p : Peer) : RetryView :=
  (p.internalId, p.timerHandshakeAttempts, p.timerRetransmitHandshake)
abbrev InitiationView := Nat × Nat × Nat × Option UInt64
def initiationView (p : Peer) : InitiationView :=
  (p.internalId, p.timerHandshakeAttempts, p.refcount, p.timerRetransmitHandshake)
abbrev WorkerView := Nat × Nat × Nat
def workerView (p : Peer) : WorkerView :=
  (p.internalId, p.timerHandshakeAttempts, p.refcount)

def retryObservation (s : Snapshot) (pid : PeerId) : Option RetryView :=
  (s.peerAt pid).map retryView
def initiationObservation (s : Snapshot) (pid : PeerId) : Option InitiationView :=
  (s.peerAt pid).map initiationView
def workerObservation (s : Snapshot) (pid : PeerId) : Option WorkerView :=
  (s.peerAt pid).map workerView

def withRecords (s : Snapshot) (records : List HiddenRecord) : Snapshot :=
  { s with ambient := { s.ambient with hidden := some records } }

def clockGap (s : Snapshot) (caller : UInt64) : Prop :=
  ∃ now, s.wg.jiffiesLast = some now ∧
    0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1
def initiationWorkerView (v : InitiationView) : WorkerView := (v.1, v.2.1, v.2.2.1)

end Leanux.Proofs.WG.TimerDiscipline
