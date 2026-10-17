import Leanux.WG.Timers

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- The give-up arm of the original retransmit callback, in source order. -/
def retransmitGiveUp (pid : PeerId) : WG.M Unit := do
  delTimer pid .sendKeepalive
  purgeStagedPackets pid
  if ← branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial) then
    discard <| modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS

end Leanux.Proofs.WG.TimerDiscipline
