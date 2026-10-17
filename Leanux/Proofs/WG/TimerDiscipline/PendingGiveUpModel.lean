import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesModel
import Leanux.Proofs.WG.Campaign2.ProductView

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The two decisions on give-up when zero-key material is pending. -/
def pendingGiveUpSteps (p : Peer) (netSection : Nat) (steps : Array Step) : Array Step :=
  (steps.push { decision := .retransmitGiveUp, outcome := true, operands := some (p.timerHandshakeAttempts, MAX_TIMER_HANDSHAKES), netRx := netSection }).push
    { decision := .retransmitZeroKeyNotPending, outcome := false, netRx := netSection }

/-- Exact full Product observation. Clearing keepalive removes its wheel entry;
the pending zero-key timer, all clocks and records, and fixture fields remain. -/
def pendingGiveUpView (entry : Campaign2.Product.Snapshot) (d : Device) (pid : PeerId) (p : Peer) : Campaign2.Product.Snapshot :=
  { entry with
    wg := { entry.wg with device := some (giveUpWheelDevice d pid p) }
    ambient := { entry.ambient with steps := pendingGiveUpSteps p entry.ambient.netRxSection entry.ambient.steps } }

end Leanux.Proofs.WG.TimerDiscipline
