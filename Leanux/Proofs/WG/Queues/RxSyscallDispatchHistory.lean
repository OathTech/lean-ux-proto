import Leanux.Proofs.WG.Queues.RxEnvControlsHistory
import Leanux.Proofs.WG.Lifetimes.SyscallsAudit

/-! Concrete syscallDispatch coverage. Only injection, flood, batch and observation
run committed RX polls inside syscallDispatch. Other explicitly enumerated source arms
use their inspected poll-free R2 observers; their later waits belong to syscall.
Socket cleanup follows every normal return, including a negative errno. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- A poll-free raw lift transports the existing audit invariant and keeps
both entry metadata and the prior release boundary unchanged. -/
theorem boundaryLift_audit (a : Leanux.M α)
    (ha : PrefixPreserves AuditInv AuditSafe (liftPrefix a)) :
    PrefixPreserves BoundaryInv BoundarySafe (liftPrefix a) := by
  apply PrefixEnsures.lift a (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have hp := (ha w (auditHistory h) hi.audit).choose_spec.2.2
  simp only [runPrefix_lift, hr] at hp
  exact ⟨hp, hi.distinct, hi.released⟩

def socketCallOn (fd : Nat) (body : Obs Int) : Obs Int := do
  let f ← liftPrefix (liftFS (fdget fd))
  if f.file.isNone then return -EBADF
  let ret ← body
  liftPrefix (liftFS (fdput f))
  return ret

theorem socketCallOn_erases (fd : Nat) (body : Obs Int) (original : Leanux.M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (socketCallOn fd body) (Leanux.socketCallOn fd original) := by
  unfold socketCallOn Leanux.socketCallOn
  syscall_wrapper_erasure

theorem socketCallOn_preserves (fd : Nat) (body : Obs Int)
    (hb : PrefixPreserves BoundaryInv BoundarySafe body) :
    PrefixPreserves BoundaryInv BoundarySafe (socketCallOn fd body) := by
  unfold socketCallOn
  repeat' first
    | exact hb
    | exact boundaryLift_audit _ (auditLift_store _ (by intro initial; exact productFS_spec _ _ (fun _ _ _ _ hi => hi)))
    | exact boundaryLift_audit _ (auditLift_store _ (by intro initial; exact productFS_spec _ _ (fun _ _ _ _ hi => hi)))
    | exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | apply PrefixPreserves.bind
    | (split <;> try simp_all only [reduceCtorEq])
    | (intro x; try dsimp only)

theorem socketCallOn_projects (fd : Nat) (body : Obs Int) (lower : AuditM Int)
    (hb : ProjectsUnder AuditInv auditEvent body lower)
    (hl : PrefixPreserves AuditInv AuditSafe lower) :
    ProjectsUnder AuditInv auditEvent (socketCallOn fd body) (socketCallOnAudit fd lower) := by
  unfold socketCallOn socketCallOnAudit
  repeat' first
    | exact hb
    | exact projectsUnder_pure _ _
    | exact projectsUnder_lift _ _
    | apply projectsUnder_bind (projectsUnder_lift _ _) (auditLift_store _ (by intro initial; exact productFS_spec _ _ (fun _ _ _ _ hi => hi)))
    | apply projectsUnder_bind (projectsUnder_lift _ _) (auditLift_store _ (by intro initial; exact productFS_spec _ _ (fun _ _ _ _ hi => hi)))
    | apply projectsUnder_bind hb hl
    | (split <;> try simp_all only [reduceCtorEq])
    | (intro x; try dsimp only)

/-- Explicit arms prevent a future source constructor from silently receiving
a whole-call frame that could hide a poll. -/
def syscallDispatch : Syscall → Obs Int
  | call@(.eventfd2 ..) => audit (dispatchAudit call)
  | call@(.dup ..) => audit (dispatchAudit call)
  | call@(.dup3 ..) => audit (dispatchAudit call)
  | call@(.close ..) => audit (dispatchAudit call)
  | call@(.read ..) => audit (dispatchAudit call)
  | call@(.write ..) => audit (dispatchAudit call)
  | call@(.pipe2 ..) => audit (dispatchAudit call)
  | call@(.fcntl ..) => audit (dispatchAudit call)
  | call@(.epollCreate1 ..) => audit (dispatchAudit call)
  | call@(.epollCtl ..) => audit (dispatchAudit call)
  | call@(.epollWait ..) => audit (dispatchAudit call)
  | call@(.wgSet ..) => audit (dispatchAudit call)
  | call@(.wgGet ..) => audit (dispatchAudit call)
  | call@(.wgGetStart ..) => audit (dispatchAudit call)
  | call@(.wgGetRecv) => audit (dispatchAudit call)
  | call@(.wgUp) => audit (dispatchAudit call)
  | call@(.wgXmit ..) => audit (dispatchAudit call)
  | call@(.wgSetMtu ..) => audit (dispatchAudit call)
  | .wgInject family port message tos ll dest => socketCallOn SENDER_FD (inject family port message tos ll dest)
  | call@(.wgDeladdr ..) => audit (dispatchAudit call)
  | call@(.wgDelroute ..) => audit (dispatchAudit call)
  | call@(.wgAddroute ..) => audit (dispatchAudit call)
  | call@(.wgAddaddr ..) => audit (dispatchAudit call)
  | .wgFlood count port family messages => flood count port family messages
  | .wgBatch items _ => batch items
  | .wgObserve => do
    let (ret, observed) ← observe
    liftPrefix (modifyAmbient fun w => { w with extraOut := ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) })
    socketCallOn LISTEN4_FD (pure ret)
  | call@(.wgAdvance ..) => audit (dispatchAudit call)
  | call@(.wgCreate) => audit (dispatchAudit call)
  | call@(.wgDown) => audit (dispatchAudit call)
  | call@(.wgDelete) => audit (dispatchAudit call)
  | call@(.wgNetnsClose) => audit (dispatchAudit call)
  | call@(.seccompInstall ..) => audit (dispatchAudit call)
  | call@(.seccompProbe ..) => audit (dispatchAudit call)
  | call@(.seccompPrctl ..) => audit (dispatchAudit call)
  | call@(.seccompCapdrop) => audit (dispatchAudit call)
  | call@(.seccompQuery ..) => audit (dispatchAudit call)

theorem syscallDispatch_erases (call : Syscall) : ErasesPrefix (syscallDispatch call) (Leanux.dispatch call) := by
  cases call
  case wgInject family port msg tos ll dest =>
    exact socketCallOn_erases _ _ _ (inject_erases family port msg tos ll dest)
  case wgFlood count port family messages => exact flood_erases count port family messages
  case wgBatch items _ => exact batch_erases items
  case wgObserve =>
    unfold syscallDispatch Leanux.dispatch
    apply erasesPrefix_bind observe_erases
    intro out
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    exact socketCallOn_erases _ _ _ (erasesPrefix_pure _)
  all_goals exact audit_erases (dispatchAudit_erases _)

theorem syscallDispatch_preserves (call : Syscall) : PrefixPreserves BoundaryInv BoundarySafe (syscallDispatch call) := by
  cases call
  case wgInject family port msg tos ll dest =>
    exact socketCallOn_preserves _ _ (inject_preserves family port msg tos ll dest)
  case wgFlood count port family messages => exact flood_preserves count port family messages
  case wgBatch items _ => exact batch_preserves items
  case wgObserve =>
    unfold syscallDispatch
    apply PrefixPreserves.bind observe_preserves
    intro out
    apply PrefixPreserves.bind (boundaryLift_kernel _ (by
      intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    intro _
    exact socketCallOn_preserves _ _ (PrefixPreserves.pure (fun _ _ hi => hi.safe) _)
  all_goals exact audit_preserves _ (dispatchAudit_preserves _)

theorem syscallDispatch_projects (call : Syscall) :
    ProjectsUnder AuditInv auditEvent (syscallDispatch call) (dispatchAudit call) := by
  cases call
  case wgInject family port msg tos ll dest =>
    exact socketCallOn_projects _ _ _ (inject_projects family port msg tos ll dest)
      (injectAudit_preserves family port msg tos ll dest)
  case wgFlood count port family messages => exact flood_projects count port family messages
  case wgBatch items _ => exact batch_projects items
  case wgObserve =>
    unfold syscallDispatch dispatchAudit
    apply projectsUnder_bind observe_projects observeAudit_preserves
    intro out
    apply projectsUnder_bind (projectsUnder_lift _ _) (auditLift_store _ (by
      intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    intro _
    exact socketCallOn_projects _ _ _ (projectsUnder_pure _ _)
      (PrefixPreserves.pure (fun _ _ hi => hi.safe) _)
  all_goals exact audit_projects (dispatchAudit_preserves _)

end Leanux.Proofs.WG.Queues.RxHistory
