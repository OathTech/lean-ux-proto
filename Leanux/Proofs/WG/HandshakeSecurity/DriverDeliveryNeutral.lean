import Leanux.Proofs.WG.TransmitSecurity.DriverSource

/-! The native delivery specialization preserves the prior source factor at
observation. Only the journal seam changes, never the native caller order. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.DriverDelivery
open Leanux Leanux.Proofs.Logged TransmitSecurity

theorem observe (hooks : Driver.Hooks E)
    (native : hooks.deliver = liftPrefix Env.deliverSent) :
    Driver.observeObserved hooks = (do
      Driver.idleTimersObserved hooks
      liftPrefix Environment.observeTail) := by
  unfold Driver.observeObserved
  rw [native,AuthenticatedEffects.DeliverySource.observe_native]

end Leanux.Proofs.WG.HandshakeSecurity.DriverDelivery
