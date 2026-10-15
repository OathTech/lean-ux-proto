import Leanux.Proofs.WG.TimerDiscipline.Model

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The two original decisions on give-up when zero-key material is pending. -/
def pendingGiveUpSteps (p : Peer) (netSection : Nat) (steps : Array Step) : Array Step :=
  (steps.push { decision := .retransmitGiveUp, outcome := true, operands := some (p.timerHandshakeAttempts, MAX_TIMER_HANDSHAKES), netRx := netSection }).push
    { decision := .retransmitZeroKeyNotPending, outcome := false, netRx := netSection }

/-- Exact projected effect, retaining all clocks, records, and other fields. -/
def pendingGiveUpView (entry : Snapshot) (d : Device) (pid : PeerId) (p : Peer) : Snapshot :=
  { entry with
    wg := { entry.wg with device := some (giveUpDevice d pid p) }
    ambient := { entry.ambient with steps := pendingGiveUpSteps p entry.ambient.netRxSection entry.ambient.steps } }

end Leanux.Proofs.WG.TimerDiscipline
