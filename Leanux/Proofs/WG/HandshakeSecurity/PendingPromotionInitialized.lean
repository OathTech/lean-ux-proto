import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionDispatch
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Pending promotion tickets on the initialized shared driver. Native frame
hypotheses are explicit; no incoming execution or history invariant is assumed.
The exact inner confirmation journal persists across later stopped callers. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open Responder.DriverCuts (hooks)

theorem initialized (facts : H1DriverFrames) (trace : Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Responder.DriverCuts.execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith ProductInv Safe
    (fun _ _ hi => hi.2.2.distinct) product_wg_stable (Driver.syscallObserved hooks)
    (syscall facts) trace placeholders
  intro w same
  apply product_wg_stable [] {w with wg := initialWG trace.net trace.bare} w same
  exact Carrier.initial trace.net trace.bare

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
