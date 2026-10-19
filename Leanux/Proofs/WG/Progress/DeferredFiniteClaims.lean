import Leanux.Proofs.WG.Progress.DeferredFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes

/-- Every original timer callback has exact finite evaluation, including
guarded keepalive allocation and any original Stop. -/
theorem TimerFinite.original_callback_finite (pid : PeerId) (timer : PeerTimer) :
    Campaign2.AgreesOn (fun _=>True) (WG.timerCallback pid timer) (TimerFinite.callback pid timer) := by
  rw [TimerFinite.callback_source]
  intro g ambient pre
  rfl

/-- The wheel dispatch unit preserves all native ordering checks, callback
outcomes and metadata-reset behavior in its finite counterpart. -/
theorem TimerFinite.original_dispatch_finite (w : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    Campaign2.Product.AgreesOn (fun _=>True) (timerDispatchUnit w pid timer entry prior)
      (TimerFinite.dispatch w pid timer entry prior) := by
  rw [TimerFinite.dispatch_source]
  intro state pre
  rfl

/-- Exact finite evaluation for every deferred constructor and every entry.
This retains native budgets and exhaustion; it does not assert useful service. -/
theorem DeferredFinite.original_evaluate_finite (call : EnvDeferredCall) :
    Campaign2.Product.AgreesOn (fun _=>True) call.original (DeferredFinite.evaluate call) := by
  rw [DeferredFinite.evaluate_source]
  intro state pre
  rfl

end Leanux.Proofs.WG.Progress
