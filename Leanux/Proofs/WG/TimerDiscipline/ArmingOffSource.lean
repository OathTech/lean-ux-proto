import Leanux.Proofs.WG.TimerDiscipline.WheelPlacementSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem armTimer_off_effect (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : Option UInt64) (entry : WGWorld) (p : Peer)
    (resident : peerAt entry pid = some p)
    (ambient after : Ambient) (final : WGWorld)
    (mode : ambient.armRecords = false)
    (run : ((armTimer pid timer delay caller).run entry).run ambient =
      .ok (((), final), after)) :
    final = wheelPlacementState entry pid p timer
      (entry.jiffiesLast.getD 0 + delay.toUInt64) (entry.jiffiesLast.getD 0) := by
  have execution : ((placeOnWheel pid timer
      (entry.jiffiesLast.getD 0 + delay.toUInt64) (entry.jiffiesLast.getD 0) none).run entry).run ambient =
      .ok (((), final), after) := by
    simpa [armTimer, getAmbient, mode, bind_pure] using run
  exact placeOnWheel_effect pid timer _ _ none entry p resident entry ambient () final after rfl execution

end Leanux.Proofs.WG.TimerDiscipline
