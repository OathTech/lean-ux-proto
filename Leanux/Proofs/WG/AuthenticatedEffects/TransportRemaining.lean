import Leanux.Proofs.WG.AuthenticatedEffects.TransportTraffic
import Leanux.Proofs.WG.AuthenticatedEffects.TransportOuter
import Leanux.Proofs.WG.Packets.PublicationRemaining

namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportControls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

theorem up : TransportChecks.Preserves (RxHistory.audit envWgUpAudit) :=
  TransportChecks.audit _ PublicationControls.up

theorem down : TransportChecks.Preserves (RxHistory.audit envWgDownAudit) :=
  TransportChecks.audit _ PublicationControls.down

theorem delete : TransportChecks.Preserves (RxHistory.audit envWgDeleteAudit) :=
  TransportChecks.audit _ PublicationControls.delete

theorem netnsCleanup : TransportChecks.Preserves (RxHistory.audit envNetnsCleanupAudit) :=
  TransportChecks.audit _ PublicationControls.netnsCleanup

theorem mtu (n : Nat) : TransportChecks.Preserves (RxHistory.audit (setMtuAudit n)) :=
  TransportChecks.audit _ (PublicationControls.mtu n)
theorem create : TransportChecks.Preserves (RxHistory.mixed (liftWGObserver wgCreatePrefix)) :=
  TransportChecks.mixed _ PublicationControls.create
end Leanux.Proofs.WG.AuthenticatedEffects.TransportControls

namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportRemaining
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransportOuter

theorem route : TransportChecks.Preserves (RxHistory.audit routeIntoWg0Audit) :=
  (audit_lift _ (lift_store _ routeIntoWg0_sameKernel)).2

theorem deladdr (family : Nat) : TransportChecks.Preserves (RxHistory.audit (wgDeladdrAudit family)) :=
  (audit_lift _ (lift_store _ (wgDeladdr_sameKernel family))).2

theorem delroute (family : Nat) : TransportChecks.Preserves (RxHistory.audit (wgDelrouteAudit family)) :=
  (audit_lift _ (lift_store _ (wgDelroute_sameKernel family))).2

theorem observe : TransportChecks.Preserves RxHistory.observe :=
  TransportDeferred.idleTimers.bind (fun _ => lift_store _ observeTail_sameKernel)

/-- Every source constructor is covered explicitly. This is a preservation
contract on arbitrary incoming histories, not an initialized-run claim. -/
theorem remaining (call : EnvRemainingCall) : TransportChecks.Preserves (RxHistory.remaining call) := by
  cases call with
  | up => exact TransportControls.up
  | mtu n => exact TransportControls.mtu n
  | route => exact route
  | down => exact TransportControls.down
  | delete => exact TransportControls.delete
  | deladdr family => exact deladdr family
  | delroute family => exact delroute family
  | observe => exact observe
  | inject family port msg tos ll dest => exact TransportTraffic.inject family port msg tos ll dest
  | flood count port family messages => exact TransportTraffic.flood count port family messages
  | inlinePoll => exact TransportChecks.pollScheduledInline
  | afterBatch => exact TransportTraffic.afterBatch
  | batch items => exact TransportTraffic.batch items
  | cleanup => exact TransportControls.netnsCleanup
  | multicast family addr =>
    exact (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TransportTraffic.«0».Leanux.Proofs.WG.AuthenticatedEffects.TransportTraffic.multicast) family addr

end Leanux.Proofs.WG.AuthenticatedEffects.TransportRemaining
