import Leanux.Proofs.WG.Progress.DeferredFiniteNativeSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.Logged

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


/-- Original selected send-worker evaluation with every native Stop retained. -/
theorem DeferredFinite.original_sendOne_finite :
    Campaign2.Product.AgreesOn (fun _=>True) Env.runOneSendWorker DeferredFinite.sendOne := by
  rw [DeferredFinite.sendOne_source]
  intro state pre
  rfl

/-- Concrete finite scheduling followed by the original delivery call. -/
theorem DeferredFinite.original_crypt_finite :
    Campaign2.Product.AgreesOn (fun _=>True) Env.runCryptWorkers
      (fun w => (runPrefix DeferredFinite.crypt w []).1) := by
  intro state pre
  exact congrArg Campaign2.Product.observeResult (DeferredFinite.crypt_erases state []).symm

/-- The original bounded send drain, including its unchanged exhaustion Stop. -/
theorem DeferredFinite.original_sendAll_finite :
    Campaign2.Product.AgreesOn (fun _=>True) Env.runSendWorkers
      (fun w => (runPrefix DeferredFinite.sendAll w []).1) := by
  intro state pre
  exact congrArg Campaign2.Product.observeResult (DeferredFinite.sendAll_erases state []).symm

end Leanux.Proofs.WG.Progress
