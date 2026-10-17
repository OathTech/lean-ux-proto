import Leanux.Proofs.WG.Packets.PublicationTraffic
import Leanux.Proofs.WG.Packets.PublicationOuter
import Leanux.Proofs.WG.Packets.PublicationControls

/-! Concrete remaining environment calls preserve the joint owner and packet
certificates on the existing journal. Both normal errno returns and failed observer prefixes
retain their original source behavior. -/
namespace Leanux.Proofs.WG.PublicationRemaining
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationOuter

theorem route : PublicationJoint.Preserves (RxHistory.audit routeIntoWg0Audit) :=
  (audit_lift _ (lift_store _ routeIntoWg0_sameKernel)).2

theorem deladdr (family : Nat) : PublicationJoint.Preserves (RxHistory.audit (wgDeladdrAudit family)) :=
  (audit_lift _ (lift_store _ (wgDeladdr_sameKernel family))).2

theorem delroute (family : Nat) : PublicationJoint.Preserves (RxHistory.audit (wgDelrouteAudit family)) :=
  (audit_lift _ (lift_store _ (wgDelroute_sameKernel family))).2

theorem observe : PublicationJoint.Preserves RxHistory.observe :=
  PublicationDeferred.idleTimers.bind (fun _ => lift_store _ observeTail_sameKernel)

/-- Every source constructor is covered explicitly. This is a preservation
contract on arbitrary incoming histories, not an initialized-run claim. -/
theorem remaining (call : EnvRemainingCall) : PublicationJoint.Preserves (RxHistory.remaining call) := by
  cases call with
  | up => exact PublicationControls.up
  | mtu n => exact PublicationControls.mtu n
  | route => exact route
  | down => exact PublicationControls.down
  | delete => exact PublicationControls.delete
  | deladdr family => exact deladdr family
  | delroute family => exact delroute family
  | observe => exact observe
  | inject family port msg tos ll dest => exact PublicationTraffic.inject family port msg tos ll dest
  | flood count port family messages => exact PublicationTraffic.flood count port family messages
  | inlinePoll => exact PublicationJoint.pollScheduledInline
  | afterBatch => exact PublicationTraffic.afterBatch
  | batch items => exact PublicationTraffic.batch items
  | cleanup => exact PublicationControls.netnsCleanup
  | multicast family addr =>
    exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.multicast) family addr

end Leanux.Proofs.WG.PublicationRemaining
