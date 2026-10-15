import Leanux.Proofs.WG.Progress.FlushQueueModel

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Campaign2 TimerDiscipline

inductive DrainSelection where
  | drained
  | send (pid : PeerId)
  | clear (pid : PeerId)
  deriving Repr, DecidableEq

def DrainSelected (d : Device) : DrainSelection → Prop
  | .drained => d.sendWorkQueue = [] ∧ d.clearWorkQueue = []
  | .send pid => pid ∈ d.sendWorkQueue
  | .clear pid => pid ∈ d.clearWorkQueue

inductive DrainReason where
  | empty
  | requestedClear (pid : PeerId)
  deriving Repr, DecidableEq

/-- Origin is assigned at the actual failing call, never inferred from its error string. -/
inductive DrainFailureOrigin where
  | selection
  | sendWorker (pid : PeerId)
  | clearWorker (pid : PeerId)
  | ownBudget
  deriving Repr, DecidableEq

structure DrainFailure where
  origin : DrainFailureOrigin
  error : Stop
  attempts : Nat

structure DrainSuccess where
  reason : DrainReason
  attempts : Nat

/-- Failed operations have no final-state field. Successful states are projected. -/
abbrev DrainOutcome := Except DrainFailure (DrainSuccess × Snapshot)

def drainAttempts : DrainOutcome → Nat
  | .error failed => failed.attempts
  | .ok (success, _) => success.attempts

def eraseDrainOutcome : DrainOutcome → Outcome Unit
  | .error failed => .error failed.error
  | .ok (_, final) => .ok ((), final)

def DrainBounded (upTo : Option PeerId) (count : Nat) (out : DrainOutcome) : Prop :=
  drainAttempts out ≤ count + 1 ∧
  match out with
  | .error failed => failed.origin ≠ .ownBudget
  | .ok (success, final) =>
    match success.reason with
    | .empty => flushQueues final = some ([], [])
    | .requestedClear pid => upTo = some pid

end Leanux.Proofs.WG.Progress
