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
theorem boundaryLift_audit (a : M α)
    (ha : PrefixPreserves AuditInv AuditSafe (liftPrefix a)) :
    PrefixPreserves BoundaryInv BoundarySafe (liftPrefix a) := by
  apply PrefixEnsures.lift a (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have hp := (ha w (auditHistory h) hi.audit).choose_spec.2.2
  simp only [runPrefix_lift, hr] at hp
  exact ⟨hp, hi.distinct, hi.released⟩

def socketCallOn (fd : Nat) (body : Obs Int) : Obs Int := do
  let f ← liftPrefix (fdget fd)
  if f.file.isNone then return -EBADF
  let ret ← body
  liftPrefix (fdput f)
  return ret

theorem socketCallOn_erases (fd : Nat) (body : Obs Int) (original : M Int)
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
    | exact boundaryLift_audit _ (auditLift_wgKernel _ (FSFrames.fdget_sameWGKernel _))
    | exact boundaryLift_audit _ (auditLift_wgKernel _ (FSFrames.fdput_sameWGKernel _))
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
    | apply projectsUnder_bind (projectsUnder_lift _ _) (auditLift_wgKernel _ (FSFrames.fdget_sameWGKernel _))
    | apply projectsUnder_bind (projectsUnder_lift _ _) (auditLift_wgKernel _ (FSFrames.fdput_sameWGKernel _))
    | apply projectsUnder_bind hb hl
    | (split <;> try simp_all only [reduceCtorEq])
    | (intro x; try dsimp only)

/-- Explicit arms prevent a future source constructor from silently receiving
a whole-call frame that could hide a poll. -/
def syscallDispatch : Syscall → Obs Int
  | call@(.eventfd2 count flags) => audit (dispatchAudit call)
  | call@(.dup fildes) => audit (dispatchAudit call)
  | call@(.dup3 oldfd newfd flags) => audit (dispatchAudit call)
  | call@(.close fd) => audit (dispatchAudit call)
  | call@(.read fd count) => audit (dispatchAudit call)
  | call@(.write fd count buf) => audit (dispatchAudit call)
  | call@(.pipe2 flags) => audit (dispatchAudit call)
  | call@(.fcntl fd cmd arg) => audit (dispatchAudit call)
  | call@(.epollCreate1 flags) => audit (dispatchAudit call)
  | call@(.epollCtl epfd op fd events data) => audit (dispatchAudit call)
  | call@(.epollWait epfd maxevents timeout) => audit (dispatchAudit call)
  | call@(.wgSet attrs) => audit (dispatchAudit call)
  | call@(.wgGet device) => audit (dispatchAudit call)
  | call@(.wgGetStart device) => audit (dispatchAudit call)
  | call@(.wgGetRecv) => audit (dispatchAudit call)
  | call@(.wgUp) => audit (dispatchAudit call)
  | call@(.wgXmit family addr payload opts) => audit (dispatchAudit call)
  | call@(.wgSetMtu mtu) => audit (dispatchAudit call)
  | .wgInject family port message tos ll dest => socketCallOn SENDER_FD (inject family port message tos ll dest)
  | call@(.wgDeladdr family) => audit (dispatchAudit call)
  | call@(.wgDelroute family) => audit (dispatchAudit call)
  | .wgFlood count port family messages => flood count port family messages
  | .wgBatch items _ => batch items
  | .wgObserve => do
    let (ret, observed) ← observe
    liftPrefix (modify fun w => { w with extraOut := ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) })
    socketCallOn LISTEN4_FD (pure ret)
  | call@(.wgAdvance ticks) => audit (dispatchAudit call)
  | call@(.wgCreate) => audit (dispatchAudit call)
  | call@(.wgDown) => audit (dispatchAudit call)
  | call@(.wgDelete) => audit (dispatchAudit call)
  | call@(.wgNetnsClose) => audit (dispatchAudit call)
  | call@(.seccompInstall via flags filter len bad mode) => audit (dispatchAudit call)
  | call@(.seccompProbe nr args where_ strict) => audit (dispatchAudit call)
  | call@(.seccompPrctl cmd args) => audit (dispatchAudit call)
  | call@(.seccompCapdrop) => audit (dispatchAudit call)
  | call@(.seccompQuery cmd action flags) => audit (dispatchAudit call)

theorem syscallDispatch_erases (call : Syscall) : ErasesPrefix (syscallDispatch call) (Leanux.dispatch call) := by
  cases call <;> first | exact audit_erases (dispatchAudit_erases _) | skip
  all_goals unfold syscallDispatch Leanux.dispatch
  all_goals repeat' first
    | exact inject_erases _ _ _ _ _ _
    | exact flood_erases _ _ _ _
    | exact batch_erases _
    | exact observe_erases
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply socketCallOn_erases
    | apply erasesPrefix_bind
    | (intro x; try dsimp only)

theorem syscallDispatch_preserves (call : Syscall) : PrefixPreserves BoundaryInv BoundarySafe (syscallDispatch call) := by
  cases call <;> first | exact audit_preserves _ (dispatchAudit_preserves _) | skip
  all_goals unfold syscallDispatch
  all_goals repeat' first
    | exact inject_preserves _ _ _ _ _ _
    | exact flood_preserves _ _ _ _
    | exact batch_preserves _
    | exact observe_preserves
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | apply socketCallOn_preserves
    | apply PrefixPreserves.bind
    | (intro x; try dsimp only)

theorem syscallDispatch_projects (call : Syscall) :
    ProjectsUnder AuditInv auditEvent (syscallDispatch call) (dispatchAudit call) := by
  cases call <;> first | exact audit_projects (dispatchAudit_preserves _) | skip
  all_goals unfold syscallDispatch dispatchAudit
  all_goals repeat' first
    | exact inject_projects _ _ _ _ _ _
    | exact flood_projects _ _ _ _
    | exact batch_projects _
    | exact observe_projects
    | exact projectsUnder_lift _ _
    | exact projectsUnder_pure _ _
    | apply socketCallOn_projects
    | exact injectAudit_preserves _ _ _ _ _ _
    | exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | apply projectsUnder_bind observe_projects observeAudit_preserves
    | apply projectsUnder_bind (projectsUnder_lift _ _) (auditLift_kernel _ (by intro w x v hr; cases hr; rfl))
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.Queues.RxHistory
