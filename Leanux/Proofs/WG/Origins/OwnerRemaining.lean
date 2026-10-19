import Leanux.Proofs.WG.Origins.OwnerTraffic
import Leanux.Proofs.WG.Origins.OwnerControlCalls

/-! Concrete remaining environment calls preserve the existing owner and
positional checks. Both normal errno returns and failed observer prefixes
retain their original source behavior. -/
namespace Leanux.Proofs.WG.OwnerRemaining
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues OwnerControlCalls

theorem route : OwnerChecks.Preserves (RxHistory.audit routeIntoWg0Audit) :=
  (audit_lift _ (lift_store _ routeIntoWg0_sameKernel)).2

theorem deladdr (family : Nat) : OwnerChecks.Preserves (RxHistory.audit (wgDeladdrAudit family)) :=
  (audit_lift _ (lift_store _ (wgDeladdr_sameKernel family))).2

theorem delroute (family : Nat) : OwnerChecks.Preserves (RxHistory.audit (wgDelrouteAudit family)) :=
  (audit_lift _ (lift_store _ (wgDelroute_sameKernel family))).2

theorem observe : OwnerChecks.Preserves RxHistory.observe :=
  OwnerDeferred.idleTimers.bind (fun _ => lift_store _ observeTail_sameKernel)

/-- Every source constructor is covered explicitly. This is a preservation
contract on arbitrary incoming histories, not an initialized-run claim. -/
theorem remaining (call : EnvRemainingCall) : OwnerChecks.Preserves (RxHistory.remaining call) := by
  cases call with
  | up => exact OwnerControlCalls.up
  | mtu n => exact OwnerControlCalls.mtu n
  | route => exact route
  | down => exact OwnerControlCalls.down
  | delete => exact OwnerControlCalls.delete
  | deladdr family => exact deladdr family
  | delroute family => exact delroute family
  | observe => exact observe
  | inject family port msg tos ll dest => exact OwnerTraffic.inject family port msg tos ll dest
  | flood count port family messages => exact OwnerTraffic.flood count port family messages
  | inlinePoll => exact OwnerWorkers.pollScheduledInline
  | afterBatch => exact OwnerTraffic.afterBatch
  | batch items => exact OwnerTraffic.batch items
  | cleanup => exact OwnerControlCalls.netnsCleanup
  | multicast family addr =>
    exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerTraffic.«0».Leanux.Proofs.WG.OwnerTraffic.multicast) family addr

end Leanux.Proofs.WG.OwnerRemaining
