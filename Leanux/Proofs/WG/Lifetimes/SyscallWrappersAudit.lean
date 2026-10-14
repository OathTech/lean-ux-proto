import Leanux.Proofs.Framing.Syscalls
import Leanux.Proofs.WG.Lifetimes.EnvRemainingCalls

/-! Literal descriptor wrappers with an arbitrary observed callback. Ordinary
negative returns follow the source cleanup path; a Stop retains its reached
history and skips all later cleanup. Filesystem effects contain no resident
WireGuard accesses. No descriptor-validity or successful-draining premise. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.Framing.KernelFrames

set_option maxHeartbeats 1000000

def socketCallOnAudit (fd : Nat) (body : AuditM Int) : AuditM Int := do
  let f ← liftPrefix (fdget fd)
  if f.file.isNone then return -EBADF
  let ret ← body
  liftPrefix (fdput f)
  return ret

def socketCallAudit (body : AuditM Int) : AuditM Int := socketCallOnAudit NETLINK_FD body

def netlinkRequestAudit (handler : AuditM Int) : AuditM Int := do
  let ret ← socketCallAudit do
    liftPrefix (skipCut allocCuts)
    let ret ← handler
    liftPrefix (skipCut allocCuts)
    pure ret
  _ ← socketCallAudit (pure 0)
  return ret

def rtnetlinkRequestAudit (handler : AuditM Int) : AuditM Int := do
  let fs ← liftPrefix getFiles
  let t := fs.fdt
  let some fd := (List.range t.maxFds).find? (fun n => n ≥ fs.nextFd && !(t.openFds.getD n true))
    | liftPrefix (unsupported "no free descriptor in the table for the temporary rtnetlink socket (expansion)")
  if fd ≥ (← liftPrefix getK).task.rlimitNofile then
    liftPrefix (unsupported "no descriptor below RLIMIT_NOFILE for the temporary rtnetlink socket (the guest fails)")
  let fid := (← liftPrefix getK).nextFile
  liftPrefix (setFile fid { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED, fCount := 1, fOp := some (.fixture "rtnetlink"), fInode := some (.fixture "rtnetlink") })
  liftPrefix (modifyK fun k => { k with nextFile := fid + 1 })
  liftPrefix (setFdtSlot fd (some fid))
  liftPrefix (setFdtOpen fd true)
  liftPrefix (setFdtCloexec fd false)
  -- the request's, the acknowledgement's and the notifications' skbs are
  -- below the cut (allocation cut sites), as in `netlinkRequest`
  let ret ← socketCallOnAudit fd do
    liftPrefix (skipCut allocCuts)
    let ret ← handler
    liftPrefix (skipCut allocCuts)
    pure ret
  _ ← socketCallOnAudit fd (pure 0)
  -- close(fd) after the window
  liftPrefix (setFdtSlot fd none)
  liftPrefix (setFdtOpen fd false)
  liftPrefix (modifyFiles fun fs => { fs with nextFd := fd })
  liftPrefix (freeFile fid)
  return ret

abbrev netnsCloseAudit : AuditM Int := liftPrefix netnsClose

macro "syscall_wrapper_erasure" : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

macro "syscall_wrapper_preservation" : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible exact auditLift_wgKernel _ (FSFrames.fdget_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.fdput_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ getFiles_sameWGKernel
    | with_reducible exact auditLift_wgKernel _ (modifyFiles_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ (setFile_sameWGKernel _ _)
    | with_reducible exact auditLift_wgKernel _ (freeFile_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ (setFdtSlot_sameWGKernel _ _)
    | with_reducible exact auditLift_wgKernel _ (setFdtOpen_sameWGKernel _ _)
    | with_reducible exact auditLift_wgKernel _ (setFdtCloexec_sameWGKernel _ _)
    | with_reducible exact auditLift_kernel _ (skipCut_sameKernel _)
    | exact auditLift_wgKernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_wgKernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem socketCallOnAudit_erases (fd : Nat) (body : AuditM Int) (original : M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (socketCallOnAudit fd body) (socketCallOn fd original) := by
  unfold socketCallOnAudit socketCallOn
  syscall_wrapper_erasure

theorem socketCallOnAudit_preserves (fd : Nat) (body : AuditM Int)
    (hb : PrefixPreserves AuditInv AuditSafe body) :
    PrefixPreserves AuditInv AuditSafe (socketCallOnAudit fd body) := by
  unfold socketCallOnAudit
  syscall_wrapper_preservation

theorem socketCallAudit_erases (body : AuditM Int) (original : M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (socketCallAudit body) (socketCall original) :=
  socketCallOnAudit_erases _ body original hb

theorem socketCallAudit_preserves (body : AuditM Int)
    (hb : PrefixPreserves AuditInv AuditSafe body) :
    PrefixPreserves AuditInv AuditSafe (socketCallAudit body) :=
  socketCallOnAudit_preserves _ body hb

theorem netlinkRequestAudit_erases (body : AuditM Int) (original : M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (netlinkRequestAudit body) (netlinkRequest original) := by
  unfold netlinkRequestAudit netlinkRequest socketCallAudit socketCall
  repeat' first | with_reducible apply socketCallOnAudit_erases | syscall_wrapper_erasure

theorem netlinkRequestAudit_preserves (body : AuditM Int)
    (hb : PrefixPreserves AuditInv AuditSafe body) :
    PrefixPreserves AuditInv AuditSafe (netlinkRequestAudit body) := by
  unfold netlinkRequestAudit socketCallAudit
  repeat' first | with_reducible apply socketCallOnAudit_preserves | syscall_wrapper_preservation

theorem rtnetlinkRequestAudit_erases (body : AuditM Int) (original : M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (rtnetlinkRequestAudit body) (rtnetlinkRequest original) := by
  unfold rtnetlinkRequestAudit rtnetlinkRequest
  repeat' first | with_reducible apply socketCallOnAudit_erases | syscall_wrapper_erasure

theorem rtnetlinkRequestAudit_preserves (body : AuditM Int)
    (hb : PrefixPreserves AuditInv AuditSafe body) :
    PrefixPreserves AuditInv AuditSafe (rtnetlinkRequestAudit body) := by
  unfold rtnetlinkRequestAudit
  repeat' first | with_reducible apply socketCallOnAudit_preserves | syscall_wrapper_preservation

theorem netnsCloseAudit_erases : ErasesPrefix netnsCloseAudit netnsClose := erasesPrefix_lift _
theorem netnsCloseAudit_preserves : PrefixPreserves AuditInv AuditSafe netnsCloseAudit :=
  auditLift_wgKernel _ SyscallFrames.netnsClose_sameWGKernel

end Leanux.Proofs.WG.Lifetimes
