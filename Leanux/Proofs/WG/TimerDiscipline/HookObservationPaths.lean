import Leanux.Proofs.WG.TimerDiscipline.ObservationPathsSource
import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

def giveUpClockPath (pid : PeerId) :
    Leanux.M (Bool × Product.Snapshot × Bool × Product.Snapshot × Option UInt64) := do
  let decision ← liftWG (retransmitDecision pid)
  let afterDecision ← Product.read
  let result ← prefixClockPath (liftWG (giveUpArmPrefix pid)) .timerJiffiesRetransmitZeroKey
  return (decision, afterDecision, result)

def initiationExecutionPath (pid : PeerId) : Leanux.M (Bool × Product.Snapshot) := do
  let reached ← liftWG (initiationArmPrefix pid)
  let beforeArm ← Product.read
  if reached then liftWG (timersHandshakeInitiated pid)
  return (reached, beforeArm)

end Leanux.Proofs.WG.TimerDiscipline
