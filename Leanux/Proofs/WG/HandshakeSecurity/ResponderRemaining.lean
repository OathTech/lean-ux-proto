import Leanux.Proofs.WG.HandshakeSecurity.ResponderTraffic

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Remaining
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Outer

theorem route : Joint.Preserves (RxHistory.audit routeIntoWg0Audit) :=
  (audit_lift _ (lift_store _ routeIntoWg0_sameKernel)).2

theorem deladdr (family : Nat) : Joint.Preserves (RxHistory.audit (wgDeladdrAudit family)) :=
  (audit_lift _ (lift_store _ (wgDeladdr_sameKernel family))).2

theorem delroute (family : Nat) : Joint.Preserves (RxHistory.audit (wgDelrouteAudit family)) :=
  (audit_lift _ (lift_store _ (wgDelroute_sameKernel family))).2

theorem observe (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Joint.Preserves RxHistory.observe :=
  (Deferred.idleTimers H1 slots).bind (fun _ => lift_store _ observeTail_sameKernel)

/-- Every source constructor is covered explicitly. This is a preservation
contract on arbitrary incoming histories, not an initialized-run claim. -/
theorem remaining (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (call : EnvRemainingCall) : Joint.Preserves (RxHistory.remaining call) := by
  cases call with
  | up => exact Controls.up
  | mtu n => exact Controls.mtu n
  | route => exact route
  | down => exact Controls.down H1
  | delete => exact Controls.delete H1
  | deladdr family => exact deladdr family
  | delroute family => exact delroute family
  | observe => exact observe H1 slots
  | inject family port msg tos ll dest => exact Traffic.inject H1 slots family port msg tos ll dest
  | flood count port family messages => exact Traffic.flood H1 slots count port family messages
  | inlinePoll => exact Traffic.pollScheduledInline H1 slots
  | afterBatch => exact Traffic.afterBatch H1 slots
  | batch items => exact Traffic.batch H1 slots items
  | cleanup => exact Controls.netnsCleanup
  | multicast family addr => exact Traffic.multicast family addr

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Remaining
