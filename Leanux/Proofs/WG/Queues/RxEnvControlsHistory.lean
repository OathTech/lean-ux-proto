import Leanux.Proofs.WG.Queues.RxEnvTimersHistory
import Leanux.Proofs.WG.Queues.RxEnvBatchHistory
import Leanux.Proofs.WG.Lifetimes.EnvRemainingCalls

/-! Remaining concrete environment callers. Observation executes the stamped
idle timer pass before its original tail. Inspected poll-free lifecycle/control
paths retain their existing focused access histories, including failed prefixes. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def observe : Obs (Int × Lean.Json) := do
  idleTimers
  liftPrefix Environment.observeTail

theorem observe_erases : ErasesPrefix observe Env.observe := by
  rw [Environment.observe_eq]
  exact erasesPrefix_bind idleTimers_erases (fun _ => erasesPrefix_lift _)

theorem observe_preserves : PrefixPreserves BoundaryInv BoundarySafe observe :=
  PrefixPreserves.bind idleTimers_preserves (fun _ => boundaryLift_kernel _ observeTail_sameKernel)

theorem observe_projects : ProjectsUnder AuditInv auditEvent observe observeAudit := by
  exact projectsUnder_bind idleTimers_projects idleTimersAudit_preserves
    (fun _ => projectsUnder_lift _ _)

/-- Explicit cases prevent a future new caller from silently inheriting a whole
focused frame. Poll-bearing cases use their concrete stamped observations. -/
def remaining : (call : EnvRemainingCall) → Obs call.Result
  | .up => audit envWgUpAudit
  | .mtu value => audit (setMtuAudit value)
  | .route => audit routeIntoWg0Audit
  | .down => audit envWgDownAudit
  | .delete => audit envWgDeleteAudit
  | .deladdr family => audit (wgDeladdrAudit family)
  | .delroute family => audit (wgDelrouteAudit family)
  | .observe => observe
  | .inject family port msg tos ll dest => inject family port msg tos ll dest
  | .flood count port family messages => flood count port family messages
  | .inlinePoll => pollScheduledInline
  | .afterBatch => afterBatch
  | .batch items => batch items
  | .cleanup => audit envNetnsCleanupAudit
  | .multicast family addr => audit (xmitMulticastLoopAudit family addr)

theorem remaining_erases (call : EnvRemainingCall) :
    ErasesPrefix (remaining call) call.original := by
  cases call with
  | up => exact audit_erases (envWgUpAudit_erases)
  | mtu value => exact audit_erases (setMtuAudit_erases value)
  | route => exact audit_erases (routeIntoWg0Audit_erases)
  | down => exact audit_erases (envWgDownAudit_erases)
  | delete => exact audit_erases (envWgDeleteAudit_erases)
  | deladdr family => exact audit_erases (wgDeladdrAudit_erases family)
  | delroute family => exact audit_erases (wgDelrouteAudit_erases family)
  | observe => exact observe_erases
  | inject family port msg tos ll dest => exact inject_erases family port msg tos ll dest
  | flood count port family messages => exact flood_erases count port family messages
  | inlinePoll => exact pollScheduledInline_erases
  | afterBatch => exact afterBatch_erases
  | batch items => exact batch_erases items
  | cleanup => exact audit_erases (envNetnsCleanupAudit_erases)
  | multicast family addr => exact audit_erases (xmitMulticastLoopAudit_erases family addr)

theorem remaining_projects (call : EnvRemainingCall) :
    ProjectsUnder AuditInv auditEvent (remaining call) call.observed := by
  cases call with
  | up => exact audit_projects (envWgUpAudit_preserves)
  | mtu value => exact audit_projects (setMtuAudit_preserves value)
  | route => exact audit_projects (routeIntoWg0Audit_preserves)
  | down => exact audit_projects (envWgDownAudit_preserves)
  | delete => exact audit_projects (envWgDeleteAudit_preserves)
  | deladdr family => exact audit_projects (wgDeladdrAudit_preserves family)
  | delroute family => exact audit_projects (wgDelrouteAudit_preserves family)
  | observe => exact observe_projects
  | inject family port msg tos ll dest => exact inject_projects family port msg tos ll dest
  | flood count port family messages => exact flood_projects count port family messages
  | inlinePoll => exact pollScheduledInline_projects
  | afterBatch => exact afterBatch_projects
  | batch items => exact batch_projects items
  | cleanup => exact audit_projects (envNetnsCleanupAudit_preserves)
  | multicast family addr => exact audit_projects (xmitMulticastLoopAudit_preserves family addr)

theorem remaining_preserves (call : EnvRemainingCall) :
    PrefixPreserves BoundaryInv BoundarySafe (remaining call) := by
  cases call with
  | up => exact audit_preserves _ (envWgUpAudit_preserves)
  | mtu value => exact audit_preserves _ (setMtuAudit_preserves value)
  | route => exact audit_preserves _ (routeIntoWg0Audit_preserves)
  | down => exact audit_preserves _ (envWgDownAudit_preserves)
  | delete => exact audit_preserves _ (envWgDeleteAudit_preserves)
  | deladdr family => exact audit_preserves _ (wgDeladdrAudit_preserves family)
  | delroute family => exact audit_preserves _ (wgDelrouteAudit_preserves family)
  | observe => exact observe_preserves
  | inject family port msg tos ll dest => exact inject_preserves family port msg tos ll dest
  | flood count port family messages => exact flood_preserves count port family messages
  | inlinePoll => exact pollScheduledInline_preserves
  | afterBatch => exact afterBatch_preserves
  | batch items => exact batch_preserves items
  | cleanup => exact audit_preserves _ (envNetnsCleanupAudit_preserves)
  | multicast family addr => exact audit_preserves _ (xmitMulticastLoopAudit_preserves family addr)

end Leanux.Proofs.WG.Queues.RxHistory
