import Leanux.Kernel.Defs

/-!
# kernel/signal.c — signal generation, down to the pending set

`send_sig` → `send_sig_info` → `do_send_sig_info` → `send_signal_locked` →
`__send_signal_locked` (with `prepare_signal`, `sig_ignored`, `legacy_queue`,
`__sigqueue_alloc`, `complete_signal`, `wants_signal`), as `pipe_write`
reaches it for `SIGPIPE` (fs/pipe.c:458, 499). User decision Q3 of the P
design (docs/2026-10-05-p-pipes.md section 6, decision P9): mirror the chain
down to the pending set.

The target `t` is a `TaskRef` (the interface commit of the seccomp design,
docs/2026-10-12-seccomp-design.md 4.1, audit M2): the trace process, which
every caller on the pipe paths passes (`current` there is the one task), or
the sandboxed child of a child probe, which the seccomp paths pass through
`Kernel.current`. Mirrored state: `t->blocked` and `t->pending.signal`. Shape deviation (design section 2): the
`sigqueue` list of `t->pending` is not mirrored (only `legacy_queue` reads
the pending set, and nothing in stage 1 dequeues), so the queued entry's
`siginfo` is not either. Cut points, each stated at its call:
`lock_task_sighand` (the task is live: it is `current` or its child),
`inc_rlimit_get_ucounts`/`dec_rlimit_put_ucounts` (kernel/ucount.c),
`signalfd_notify` (no signalfd waiters), `task_pid_nr_ns`,
`from_kuid_munged`, `trace_signal_generate`.

Paths outside the stage (`unsupported`): an unblocked signal (handler
dispositions are not mirrored), stop and continue signals, shared or
process-group delivery, real-time signals, a thread that wants the signal
(`signal_wake_up`).
-/

namespace Leanux

/-- Signal numbers (arch/x86/include/uapi/asm/signal.h) and limits. -/
def SIGKILL : Nat := 9
def SIGCONT : Nat := 18
def SIGRTMIN : Nat := 32
/-- `_NSIG` (arch/x86/include/asm/signal.h). -/
def NSIG : Nat := 64

/-- `enum pid_type` (include/linux/pid_types.h): PIDTYPE_PID = 0,
    PIDTYPE_TGID = 1, ... -/
def PIDTYPE_PID : Nat := 0
def PIDTYPE_TGID : Nat := 1

/-- The `info` argument: `SEND_SIG_NOINFO` (`(struct kernel_siginfo *) 0`) or
    `SEND_SIG_PRIV` (`1`), the two special values (`is_si_special`). A real
    `siginfo` never arises on these paths. -/
inductive SigInfo where
  | noinfo | priv
  deriving Repr, BEq

/-- `sig_kernel_stop(sig)` (include/linux/signal.h): `sig < SIGRTMIN` and `sig`
    in `SIG_KERNEL_STOP_MASK` = {SIGSTOP 19, SIGTSTP 20, SIGTTIN 21,
    SIGTTOU 22}. A value, not a mirrored choice point of its own. -/
def sigKernelStop (sig : Nat) : Bool := sig < SIGRTMIN && [19, 20, 21, 22].contains sig

#guard [19, 20, 21, 22].all sigKernelStop && !sigKernelStop SIGPIPE && !sigKernelStop SIGCONT

/-- __sigqueue_alloc (kernel/signal.c:404-442). `inc_rlimit_get_ucounts` is a
    cut point with the contract: the per-user pending count after the
    increment, nonzero (no overflow). Its value is not observable to the
    mirror: the condition at 425 is the cut's outcome. Returns whether a
    `sigqueue` was allocated (`q != NULL`). -/
def sigqueueAlloc (overrideRlimit : Nat) : M Bool := do
  -- rcu_read_lock(); ucounts = task_ucounts(t); sigpending = inc_rlimit_get_ucounts(...)
  let sigpendingNonzero := true  -- the cut's contract
  if ← branch .sigqueueAllocNoUcounts (!sigpendingNonzero) then return false
  -- `override_rlimit || likely(sigpending <= task_rlimit(t, RLIMIT_SIGPENDING))`
  let q ← do
    if ← branchCmp .sigqueueAllocOverride (overrideRlimit != 0) overrideRlimit 0 then
      envOk .sigqueueAlloc  -- kmem_cache_alloc(sigqueue_cachep, gfp_flags)
    else
      unsupported "__sigqueue_alloc without override_rlimit (RLIMIT_SIGPENDING)"
  if ← branch .sigqueueAllocNull (!q) then
    pure ()  -- dec_rlimit_put_ucounts: a cut
  -- else INIT_LIST_HEAD(&q->list); q->flags; q->ucounts (the list is not mirrored)
  return q

/-- sig_ignored (kernel/signal.c:104-123), for the target `t`.
    `t->real_blocked` is empty (it is set only inside `sigtimedwait`). -/
def sigIgnored (t : TaskRef) (sig : Nat) : M Bool := do
  let t ← getTask t
  -- `sigismember(&t->blocked, sig) || sigismember(&t->real_blocked, sig)`
  let blocked ← do
    if ← branch .sigIgnoredBlocked (sigismember t.blocked sig) then pure true
    else branch .sigIgnoredRealBlocked (sigismember (0 : SigSet) sig)
  if blocked then return false
  -- `t->ptrace && sig != SIGKILL`: the trace child is not traced
  if ← branch .sigIgnoredPtrace false then return false
  unsupported "sig_task_ignored: an unblocked signal's disposition"

/-- prepare_signal (kernel/signal.c:902-967), for the target `t`. -/
def prepareSignal (t : TaskRef) (sig : Nat) : M Bool := do
  -- `signal->flags & SIGNAL_GROUP_EXIT`: the trace child is not exiting
  if ← branch .prepareSignalGroupExit false then
    unsupported "prepare_signal: a group exit in progress"
  else if ← branch .prepareSignalStop (sigKernelStop sig) then
    unsupported "prepare_signal: a stop signal"
  else if ← branchCmp .prepareSignalCont (sig == SIGCONT) sig SIGCONT then
    unsupported "prepare_signal: SIGCONT"
  return !(← sigIgnored t sig)

/-- legacy_queue (kernel/signal.c:1068-1071) on `t->pending`. -/
def legacyQueue (pending : SigSet) (sig : Nat) : M Bool := do
  if ← branchCmp .legacyQueueNotRt (sig < SIGRTMIN) sig SIGRTMIN then
    branch .legacyQueuePending (sigismember pending sig)
  else return false

/-- wants_signal (kernel/signal.c:977-992), for the target `t`. -/
def wantsSignal (t : TaskRef) (sig : Nat) : M Bool := do
  if ← branch .wantsSignalBlocked (sigismember (← getTask t).blocked sig) then return false
  unsupported "wants_signal: an unblocked signal (PF_EXITING, task_curr, task_sigpending)"

/-- complete_signal (kernel/signal.c:994-1066), for the target `t`. -/
def completeSignal (t : TaskRef) (sig : Nat) (type : Nat) : M Unit := do
  if ← branch .completeSignalWants (← wantsSignal t sig) then
    unsupported "complete_signal: a thread to wake (signal_wake_up)"
  -- `(type == PIDTYPE_PID) || thread_group_empty(p)`
  if ← branchCmp .completeSignalPidType (type == PIDTYPE_PID) type PIDTYPE_PID then
    return  -- one thread, which does not need to be woken
  unsupported "complete_signal: thread_group_empty (group delivery)"

/-- __send_signal_locked (kernel/signal.c:1073-1188), with `t->sighand->siglock`
    held, for the target `t`. Returns `ret` (0, or -EAGAIN on a queue
    overflow). -/
def sendSignalLocked' (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) (_force : Bool) : M Int := do
  -- result = TRACE_SIGNAL_IGNORED
  if ← branch .sendSignalNotPrepared !(← prepareSignal t sig) then return 0
  -- `pending = (type != PIDTYPE_PID) ? &t->signal->shared_pending : &t->pending`
  if ← branchCmp .sendSignalShared (type != PIDTYPE_PID) type PIDTYPE_PID then
    unsupported "__send_signal_locked: shared_pending"
  -- result = TRACE_SIGNAL_ALREADY_PENDING
  if ← branch .sendSignalLegacy (← legacyQueue (← getTask t).pending sig) then return 0
  -- result = TRACE_SIGNAL_DELIVERED
  -- `(sig == SIGKILL) || (t->flags & PF_KTHREAD)`
  let skip ← do
    if ← branchCmp .sendSignalSigkill (sig == SIGKILL) sig SIGKILL then pure true
    else branch .sendSignalKthread (← getTask t).isKthread
  if !skip then
    let overrideRlimit : Nat ← do
      if ← branch .sendSignalNotRt (sig < SIGRTMIN) then
        -- `is_si_special(info) || info->si_code >= 0`: both info values are special
        if ← branch .sendSignalSiSpecial true then pure 1
        else unsupported "__send_signal_locked: a real siginfo"
      else pure 0
    let q ← sigqueueAlloc overrideRlimit
    if ← branch .sendSignalQueued q then
      -- list_add_tail(&q->list, &pending->list): the list is not mirrored
      match info with
      | .noinfo =>
        -- si_signo, si_errno, si_code = SI_USER, si_pid, si_uid: not mirrored
        _ ← branch .sendSignalNoinfo true
      | .priv => _ ← branch .sendSignalPrivInfo true
    else
      -- `!is_si_special(info) && sig >= SIGRTMIN && info->si_code != SI_USER`
      if ← branch .sendSignalOverflowNotSpecial false then
        unsupported "__send_signal_locked: a real-time queue overflow"
      -- result = TRACE_SIGNAL_LOSE_INFO
  -- out_set: signalfd_notify(t, sig) is a cut (no signalfd waiters)
  modifyTask t fun tk => { tk with pending := sigaddset tk.pending sig }
  if ← branchCmp .sendSignalMultiprocess (type > PIDTYPE_TGID) type PIDTYPE_TGID then
    unsupported "__send_signal_locked: multiprocess signals"
  completeSignal t sig type
  -- ret: trace_signal_generate (a tracepoint, compiled to a static branch)
  return 0

/-- send_signal_locked (kernel/signal.c:1214-1252). `force` for
    `SEND_SIG_NOINFO` is `!task_pid_nr_ns(current, ...)`, an assignment (not
    a choice point): the trace child's pid is nonzero, so `false`. -/
def sendSignalLocked (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) : M Int := do
  let force ← do
    if ← branch .sendSignalLockedNoinfo (info == .noinfo) then
      pure false  -- force = !task_pid_nr_ns(current, task_active_pid_ns(t))
    else if ← branch .sendSignalLockedPriv (info == .priv) then pure true
    else unsupported "send_signal_locked: has_si_pid_and_uid"
  sendSignalLocked' t sig info type force

/-- do_send_sig_info (kernel/signal.c:1297-1309). `lock_task_sighand` is a cut
    point: the target is live (`current`, or the child inside its probe), so
    it succeeds. -/
def doSendSigInfo (t : TaskRef) (sig : Nat) (info : SigInfo) (type : Nat) : M Int := do
  let mut ret : Int := -3  -- -ESRCH
  if ← branch .doSendSigLock true then
    ret ← sendSignalLocked t sig info type
    -- unlock_task_sighand
  return ret

/-- send_sig_info (kernel/signal.c:1656-1666) to the target `t`. -/
def sendSigInfo (t : TaskRef) (sig : Nat) (info : SigInfo) : M Int := do
  -- `!valid_signal(sig)`: `sig <= _NSIG` (include/linux/signal.h:274)
  if ← branchCmp .sendSigInfoInvalid (!(sig <= NSIG)) sig NSIG then return -EINVAL
  doSendSigInfo t sig info PIDTYPE_PID

/-- send_sig (kernel/signal.c:1672-1676) to the target `t` (`current` on
    the pipe paths: `.task`). -/
def sendSig (t : TaskRef) (sig : Nat) (priv : Nat) : M Int := do
  -- `__si_special(priv)`: `priv ? SEND_SIG_PRIV : SEND_SIG_NOINFO`
  let info : SigInfo := if ← branchCmp .sendSigPriv (priv != 0) priv 0 then .priv else .noinfo
  sendSigInfo t sig info

end Leanux
