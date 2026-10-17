import Leanux.Proofs.WG.TimerDiscipline.Model

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- Current give-up prefix clears both the keepalive expiry and wheel slot. -/
def giveUpWheelPeer (p : Peer) : Peer :=
  {((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none) with staged := []}

def giveUpWheelDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  { d with
    peers := (d.peers.insert pid ((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none)).insert pid (giveUpWheelPeer p)
    txDropped := d.txDropped + p.staged.length }

end Leanux.Proofs.WG.TimerDiscipline
