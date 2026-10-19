import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryConfiguration

/-! History contracts include every send callback reached by shutdown and
deletion; no assumption that their native guards exclude queued work is used. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.SendExchange
variable {E : Type} {Safe : List E → Prop} {g : Hooks E}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem down_history (h : ActorHistorySafe Safe g) :
    StateHistorySafe Safe (downObserved g) := by
  unfold downObserved downWith stopWith timersStopWith
  repeat' first
    | (driver_history_head sendDrainObserved; exact sendDrain_history h _)
    | driver_state_history_step

theorem destruct_history (h : ActorHistorySafe Safe g) :
    StateHistorySafe Safe (destructObserved g) := by
  change StateHistorySafe Safe
    (Configuration.destructWith liftWGPrefix (removeAllObserved g) _)
  unfold Configuration.destructWith
  repeat' first
    | (driver_history_head removeAllObserved; exact removeAll_history h)
    | driver_state_history_step

theorem envDown_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (envDownObserved g) := by
  unfold envDownObserved envDownWith
  repeat' first
    | (driver_history_head downObserved; exact (down_history h).liftWGObserver)
    | driver_product_history_step

theorem envDelete_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (envDeleteObserved g) := by
  unfold envDeleteObserved envDeleteWith Configuration.envDeleteWith
  repeat' first
    | (driver_history_head downObserved; exact (down_history h).liftWGObserver)
    | (driver_history_head destructObserved; exact (destruct_history h).liftWGObserver)
    | driver_product_history_step

end Leanux.Proofs.WG.TransmitSecurity.Driver
