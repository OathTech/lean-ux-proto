import Leanux.Proofs.WG.TimerDiscipline.GuardedArmingClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The actual traversal hook has a resident peer at entry. Its complete WG
arm effect holds in either record mode when interval/running/live enable it;
otherwise the WG state is unchanged. This relates the immediate hook states,
not the eventual receiver state or packet delivery. -/
def TraversalAllModeEffect (pid : PeerId) (before after : Campaign2.Snapshot) : Prop :=
  ∃ d p, before.wg.device = some d ∧ d.peers[pid]? = some p ∧
    if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false then
      peerTimerArmEffect before pid p .persistentKeepalive
        (p.persistentKeepaliveInterval * HZ) after.wg
    else after.wg = before.wg

end Leanux.Proofs.WG.TimerDiscipline
