import Leanux.Proofs.WG.TimerDiscipline.ObservationPathsSource
import Leanux.Proofs.WG.TimerDiscipline.ObservationProductSource
import Leanux.Proofs.WG.TimerDiscipline.SourceClaims
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.TimerDiscipline.View

/-! Source connection for projected timer observations. Every inspection starts
at the same concrete entry as the original action; every first internally
threads its actual state. No state is reconstructed from an observation. -/
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

def giveUpClockPath (pid : PeerId) :
    M (Bool × Snapshot × Bool × Snapshot × Option UInt64) := do
  let decision ← retransmitDecision pid
  let afterDecision ← Campaign2.read
  let result ← prefixClockPath (giveUpArmPrefix pid) .timerJiffiesRetransmitZeroKey
  return (decision, afterDecision, result)

def timerExecutionPath (worker : Worker) (horizon : UInt64) : M (PeerId × PeerTimer × Snapshot) := do
  let selected ← timerSelection worker horizon
  let beforeCallback ← Campaign2.read
  fireSelected worker selected.1 selected.2
  return (selected.1, selected.2, beforeCallback)

def initiationExecutionPath (pid : PeerId) : M (Bool × Snapshot) := do
  let reached ← initiationArmPrefix pid
  let beforeArm ← Campaign2.read
  if reached then timersHandshakeInitiated pid
  return (reached, beforeArm)

end Leanux.Proofs.WG.TimerDiscipline
