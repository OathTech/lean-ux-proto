import Leanux.Seccomp.Bridge
import Leanux.Kernel.Signal
import Leanux.Kernel.Refcount

/-!
# kernel/seccomp.c — seccomp proper

seccomp stream V (docs/2026-10-12-seccomp-design.md, 2.1-2.4, 2.8-2.10, 4.5):
the entry (`__secure_computing`, the strict table, `__seccomp_filter` with
every action arm in the C's order), the chain walk with the cache
(`seccomp_run_filters`, `seccomp_cache_check_allow_bitmap`), the install
(`seccomp_set_mode_filter`, `seccomp_prepare_user_filter`,
`seccomp_prepare_filter`, `seccomp_attach_filter`, `seccomp_cache_prepare`
with the C's `seccomp_is_const_allow`), strict mode, `do_seccomp` and
`prctl_set_seccomp`, the queries, `get_seccomp_filter` (the parent's clone),
and `seccomp_filter_free` at a failed attach.

The engine seam is `seccomp_run_filters`'s `bpf_prog_run_pin_on_cpu`
(:426): `seccompRunFilters` is parametric in a `BpfEngine` instance
(design 4.4); the differential check runs `MiniInterp`.

Cuts, each named at its call: `arch_seccomp_spec_mitigate` (speculation
control bits no operation observes), `disable_TSC`, `smp_*` barriers and
the locks, `mutex_init` and `init_waitqueue_head` on the new filter (the
notifier is not mirrored, 9.2), `syscall_rollback` and
`syscall_set_return_value` (the register effects are the outcome's return
value), `populate_seccomp_data` (the data is the operation's), `audit_seccomp`
(empty with AUDIT unset), `bpf_prog_free` (`kernel/bpf/core.c`),
`kick_process`. Out of scope (`unsupported`): `TSYNC`, `NEW_LISTENER`,
`WAIT_KILLABLE_RECV`, `USER_NOTIF`, a tracer. Dead in this domain
(`invariant`): `SECCOMP_MODE_DEAD` at entry, the `do_exit(SIGSYS)` arm, a
NULL head under mode filter.

Every repeatable decision (the entry path, the strict table, the chain walk,
the cache's emulation) is emitted once per operation through
`Leanux.Seccomp.kbranch` (design 4.2, 4.5).
-/

namespace Leanux.Seccomp

/-- `SECCOMP_FILTER_FLAG_*` (include/uapi/linux/seccomp.h:21-27) and the mask. -/
def SECCOMP_FILTER_FLAG_TSYNC : UInt32 := 1
def SECCOMP_FILTER_FLAG_LOG : UInt32 := 2
def SECCOMP_FILTER_FLAG_SPEC_ALLOW : UInt32 := 4
def SECCOMP_FILTER_FLAG_NEW_LISTENER : UInt32 := 8
def SECCOMP_FILTER_FLAG_TSYNC_ESRCH : UInt32 := 16

def errESRCH : Int := -3
def SECCOMP_FILTER_FLAG_WAIT_KILLABLE_RECV : UInt32 := 32
def SECCOMP_FILTER_FLAG_MASK : UInt32 := 63

/-- `SECCOMP_SET_MODE_STRICT` ... `SECCOMP_GET_NOTIF_SIZES` (uapi seccomp.h:15-18). -/
def SECCOMP_SET_MODE_STRICT : Nat := 0
def SECCOMP_SET_MODE_FILTER : Nat := 1
def SECCOMP_GET_ACTION_AVAIL : Nat := 2
def SECCOMP_GET_NOTIF_SIZES : Nat := 3

/-- `MAX_ERRNO` (include/linux/err.h) and `MAX_INSNS_PER_PATH` (seccomp.c:240). -/
def MAX_ERRNO : Int := 4095
def MAX_INSNS_PER_PATH : Nat := 32768

/-- `ENOSYS`, `EACCES`, `EBUSY`, `EOPNOTSUPP` as the C returns them. -/
def errENOSYS : Int := -38
def errEACCES : Int := -13
def errEBUSY : Int := -16
def errEOPNOTSUPP : Int := -95

/-- The x86-64 numbers of `mode1_syscalls` (seccomp.c:1048-1057): read, write,
    exit, rt_sigreturn, uretprobe; `-1` terminates the table. -/
def mode1Syscalls : List Int := [0, 1, 60, 15, NR_URETPROBE]

/-- `seccomp.mode` as the C compares it (`SECCOMP_MODE_DISABLED` 0, `_STRICT` 1,
    `_FILTER` 2, `SECCOMP_MODE_DEAD` 3). -/
def _root_.Leanux.SeccompMode.num : SeccompMode → Nat
  | .disabled => 0 | .strict => 1 | .filter => 2 | .dead => 3

/-- The outcome of `__secure_computing` for one system call (design 4.5):
    the call proceeds; it is skipped with this return value (`ERRNO`, the
    tracer-less `TRACE`); a `SIGSYS` with a handler was generated (`TRAP`:
    the call returns its own number after the handler, 2.2); the task was
    killed with this signal (`SIGSYS` by a filter, `SIGKILL` by strict mode). -/
inductive FilterOutcome where
  | proceed
  | skip (ret : Int)
  | trapped (nr data : Int)
  | killed (sig : Nat)
  deriving Repr, BEq

/-- `ACTION_ONLY(ret)` (seccomp.c:396): `(s32)(ret & SECCOMP_RET_ACTION_FULL)`. -/
def actionOnly (ret : UInt32) : Int := s32 (ret &&& SECCOMP_RET_ACTION_FULL)

def getFilter (id : FilterId) : M SeccompFilter := do
  match (← getK).seccompFilters.get? id with
  | some f => return f
  | none => _root_.Leanux.invariant s!"seccomp filter {id} is not allocated"

def modifyFilter (id : FilterId) (f : SeccompFilter → SeccompFilter) : M Unit := do
  let flt ← getFilter id
  modifyK fun k => { k with seccompFilters := k.seccompFilters.insert id (f flt) }

/-- The current task's `seccomp` state, updated. -/
def modifySeccomp (f : SeccompState → SeccompState) : M Unit := do
  let t := (← getTasks).current
  modifyTask t fun tk => { tk with seccomp := f tk.seccomp }

/-! ## The cache: seccomp_uprobe_exception, seccomp_is_const_allow, seccomp_cache_prepare (:736-898) -/

/-- seccomp_uprobe_exception (:736-754): native-only, `nr == __NR_uretprobe`. -/
def seccompUprobeException (sd : SeccompData) : M Bool := do
  if ← kbranchCmp .uprobeExceptionUretprobe (sd.nr == NR_URETPROBE) sd.nr NR_URETPROBE then return true
  return false

/-- Which arm of `seccomp_is_const_allow`'s switch an instruction takes. -/
private inductive ConstArm where
  | ldAbs | retK | ja | jcond | andK | other

private def constArm (code : UInt16) : ConstArm :=
  if code == (BPF_LD ||| BPF_W ||| BPF_ABS) then .ldAbs
  else if code == (BPF_RET ||| BPF_K) then .retK
  else if code == (BPF_JMP ||| BPF_JA) then .ja
  else if code == (BPF_JMP ||| BPF_JEQ ||| BPF_K) || code == (BPF_JMP ||| BPF_JGE ||| BPF_K)
      || code == (BPF_JMP ||| BPF_JGT ||| BPF_K) || code == (BPF_JMP ||| BPF_JSET ||| BPF_K) then .jcond
  else if code == (BPF_ALU ||| BPF_AND ||| BPF_K) then .andK
  else .other

/-- seccomp_is_const_allow (:762-836) with the C's decisions, over the
    un-rewritten `orig_prog` (2.6): the uretprobe exception, then the
    one-register emulation. A switch arm is recorded (true) when taken. The
    loop is bounded by the program's length: a checked program ends in a
    `RET` within `len` steps, and the fall-off is the C's `WARN_ON` (9.3). -/
def seccompIsConstAllow (prog : _root_.Leanux.ClassicProg) (sd : SeccompData) : M Bool := do
  -- WARN_ON_ONCE(!fprog): orig_prog is always saved (save_orig, 2.4)
  if ← kbranch .constAllowNoFprog false then return false
  if ← kbranch .constAllowException (← seccompUprobeException sd) then return true
  let mut reg : UInt32 := 0
  let mut pc := 0
  let len := prog.size
  for _ in [0:len + 1] do
    if !(← kbranch .constAllowLoop (pc < len)) then
      -- ran off the end: WARN_ON(1), modelled and unexercised (design 9.3)
      return false
    let insn := prog[pc]!
    let k := insn.k
    match constArm insn.code with
    | .ldAbs =>
      _ ← kbranch .constAllowCaseLdAbs true
      if ← kbranch .constAllowLdNr (k == 0) then reg := sd.nrWord
      else if ← kbranch .constAllowLdArch (k == 4) then reg := sd.arch
      else
        _ ← kbranch .constAllowLdOther true
        return false   -- can't optimize (non-constant value load)
    | .retK =>
      _ ← kbranch .constAllowCaseRet true
      return ← kbranchCmp .constAllowRetAllow (k == SECCOMP_RET_ALLOW) (u32 k) (u32 SECCOMP_RET_ALLOW)
    | .ja =>
      _ ← kbranch .constAllowCaseJa true
      pc := pc + k.toNat
    | .jcond =>
      _ ← kbranch .constAllowCaseJcond true
      let op := bpfOp insn.code
      let res ← do
        if op == BPF_JEQ then
          _ ← kbranch .constAllowJeq true
          kbranchCmp .constAllowJeqRes (reg == k) (u32 reg) (u32 k)
        else if op == BPF_JGE then
          _ ← kbranch .constAllowJge true
          kbranchCmp .constAllowJgeRes (reg ≥ k) (u32 reg) (u32 k)
        else if op == BPF_JGT then
          _ ← kbranch .constAllowJgt true
          kbranchCmp .constAllowJgtRes (reg > k) (u32 reg) (u32 k)
        else
          _ ← kbranch .constAllowJset true
          -- `!!(reg_value & k)` is compiled as `(reg_value & k) != 0`: the variable is the
          -- masked value, the constant 0 (measured on sc2 by X, seccomp-generated: records
          -- (0x0, 0x0) and (0x0, 0x68))
          kbranchCmp .constAllowJsetRes ((reg &&& k) != 0) (u32 (reg &&& k)) 0
      -- `pc += op_res ? insn->jt : insn->jf`
      pc := pc + (if ← kbranch .constAllowJumpTaken res then insn.jt.toNat else insn.jf.toNat)
    | .andK =>
      _ ← kbranch .constAllowCaseAnd true
      reg := reg &&& k
    | .other =>
      _ ← kbranch .constAllowCaseDefault true
      return false   -- can't optimize (unknown insn)
    pc := pc + 1
  _root_.Leanux.invariant "seccomp_is_const_allow: the emulation did not end within len + 1 steps"

/-- seccomp_cache_prepare (:881-898) through seccomp_cache_prepare_bitmap
    (:839-873), native only: the previous filter's bitmap or all ones, then
    every set bit is kept iff the program is constantly `ALLOW` for it. -/
def seccompCachePrepare (id : FilterId) : M Unit := do
  let f ← getFilter id
  let prev ← match f.prev with
    | some p => pure (some (← getFilter p).allowNative)
    | none => pure none
  let mut bitmap : BitVec NR_syscalls ←
    if ← kbranch .cachePrepareHasPrev prev.isSome then pure prev.get!   -- bitmap_copy
    else pure (BitVec.allOnes NR_syscalls)   -- bitmap_fill
  for nr in [0:NR_syscalls] do
    _ ← kbranch .cachePrepareNr true
    if ← kbranch .cachePrepareBitClear (!bitmap.getLsbD nr) then continue
    let sd : SeccompData := { nr := nr, arch := AUDIT_ARCH_X86_64 }
    if ← kbranch .cachePrepareConstAllow (← seccompIsConstAllow f.origProg sd) then continue
    bitmap := bitmap &&& ~~~(1#NR_syscalls <<< nr)   -- __clear_bit
  _ ← kbranch .cachePrepareNr false
  modifyFilter id fun f => { f with allowNative := bitmap }

/-! ## Running: seccomp_cache_check_allow_bitmap, seccomp_run_filters (:351-434) -/

/-- seccomp_cache_check_allow_bitmap (:351-360) through the native-only
    `seccomp_cache_check_allow` (:369-394): a number outside `0..462` is never
    cached; `array_index_nospec` is an identity here. -/
def seccompCacheCheckAllow (allow : BitVec NR_syscalls) (nr : Int) : M Bool := do
  -- `syscall_nr < 0 || syscall_nr >= bitmap_size`: one line, one body
  if ← kbranchCmp .cacheNrNegative (nr < 0) nr 0 then return false
  if ← kbranchCmp .cacheNrOverSize (nr ≥ NR_syscalls) nr NR_syscalls then return false
  kbranch .cacheBitSet (allow.getLsbD nr.toNat)

/-- seccomp_run_filters (:406-434): the cache, then every filter from the
    head through `prev`, keeping the lowest `ACTION_ONLY`; `*match` is the
    filter that set it. The engine seam is :426 (design 4.4). -/
def seccompRunFilters {E : Type} [BpfEngine E] (e : E) (sd : SeccompData) : M (UInt32 × Option FilterId) := do
  let tk ← getCurrent
  let mut ret := SECCOMP_RET_ALLOW
  let mut matched : Option FilterId := none
  if ← kbranch .runFiltersNullHead tk.seccomp.filter.isNone then
    _root_.Leanux.invariant "seccomp_run_filters: no filter under SECCOMP_MODE_FILTER (WARN_ON)"
  let head ← getFilter tk.seccomp.filter.get!
  if ← kbranch .runFiltersCacheHit (← seccompCacheCheckAllow head.allowNative sd.nr) then
    return (SECCOMP_RET_ALLOW, none)
  let mut f : Option FilterId := some head.id
  for _ in [0:tk.seccomp.filterCount + 1] do
    if !(← kbranch .runFiltersLoop f.isSome) then break
    let flt ← getFilter f.get!
    -- bpf_prog_run_pin_on_cpu(f->prog, sd): the engine
    let cur ← match BpfEngine.run e (progOfFilter flt) sd with
      | .ok v => pure v
      | .error (.unsupportedRead off) =>
        _root_.Leanux.unsupported s!"the filter reads the instruction pointer (seccomp_data offset {off}; design 3.2)"
      | .error (.unsupportedInsn pc code) =>
        _root_.Leanux.invariant s!"the engine met an opcode the translation never emits ({code} at {pc})"
      | .error (.fault what) => _root_.Leanux.invariant s!"the engine faulted on a checked program: {what}"
    if ← kbranchCmp .runFiltersLower (actionOnly cur < actionOnly ret) (actionOnly cur) (actionOnly ret) then
      ret := cur
      matched := some flt.id
    f := flt.prev
  if f.isSome then _root_.Leanux.invariant "seccomp_run_filters: the chain is longer than filter_count"
  return (ret, matched)

/-! ## seccomp_log (:1000-1041) -/

/-- seccomp_log: the switch on the action and the final test. Every action
    but `ALLOW` is in the default `seccomp_actions_logged` (:992-998; the
    fixture row checks the sysctl, design 3.2). `audit_seccomp` is empty
    with AUDIT unset, so the effect is nothing; the decisions are mirrored
    (2.2) and may own no instrumentation if the compiler dropped them. -/
def seccompLog (_syscall : Int) (_signr : Nat) (action : UInt32) (requested : Bool) : M Unit := do
  let log ← do
    if action == SECCOMP_RET_ALLOW then
      _ ← kbranch .logCaseAllow true
      pure false
    else if action == SECCOMP_RET_TRAP then
      _ ← kbranch .logCaseTrap true
      kbranch .logTrapRequested requested
    else if action == SECCOMP_RET_ERRNO then
      _ ← kbranch .logCaseErrno true
      kbranch .logErrnoRequested requested
    else if action == SECCOMP_RET_TRACE then
      _ ← kbranch .logCaseTrace true
      kbranch .logTraceRequested requested
    else if action == SECCOMP_RET_USER_NOTIF then
      _ ← kbranch .logCaseUserNotif true
      kbranch .logUserNotifRequested requested
    else if action == SECCOMP_RET_LOG then
      _ ← kbranch .logCaseLog true
      pure true
    else if action == SECCOMP_RET_KILL_THREAD then
      _ ← kbranch .logCaseKillThread true
      pure true
    else
      _ ← kbranch .logCaseKillProcess true   -- KILL_PROCESS and default
      pure true
  if ← kbranch .logNotLogged (!log) then return
  -- audit_seccomp(syscall, signr, action): empty (CONFIG_AUDIT unset)

/-! ## The entry: __seccomp_filter, __secure_computing_strict, __secure_computing (:1059-1077, :1244-1404) -/

/-- __seccomp_filter (:1244-1366) with `recheck_after_trace = false`. The
    data comes from the operation (`populate_seccomp_data` is a cut: the C's
    `sd` is NULL at entry, :1258). `syscall_rollback` and
    `syscall_set_return_value` are register effects carried by the outcome. -/
def seccompFilter {E : Type} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) : M FilterOutcome := do
  if ← kbranch .filterNoSd true then pure ()   -- populate_seccomp_data(&sd_local)
  -- the instruction pointer the C stores there (:265), recorded at that line
  -- (kind 312, HiddenSite.seccompIp): a filter loading offsets 8..15 branches on it
  let sd : SeccompData := { sd with ip := some (UInt64.ofNat (← hiddenU64 .seccompIp)) }
  let (filterRet, matched) ← seccompRunFilters e sd
  let data : Int := (filterRet &&& SECCOMP_RET_DATA).toNat
  let action := filterRet &&& SECCOMP_RET_ACTION_FULL
  -- skip: seccomp_log(this_syscall, 0, action, match ? match->log : false); return -1
  let skip (outcome : FilterOutcome) : M FilterOutcome := do
    let requested ← do
      if ← kbranch .filterSkipMatchLog matched.isSome then pure (← getFilter matched.get!).log
      else pure false
    seccompLog nr 0 action requested
    return outcome
  if action == SECCOMP_RET_ERRNO then
    _ ← kbranch .filterCaseErrno true
    -- `data > MAX_ERRNO` is compiled as `(data & ~0xfff) != 0`: the variable is the masked
    -- data, the constant 0 (measured on sc2, X: the record is (0x0, 0x1000) for 4096 and
    -- (0x0, 0xf000) for 65535, KCOV's constant first)
    let data ← if ← kbranchCmp .filterErrnoCap (data > MAX_ERRNO) (Int.ofNat (data.toNat &&& 0xfffff000)) 0 then pure MAX_ERRNO else pure data
    -- syscall_set_return_value(current, regs, -data, 0)
    skip (.skip (-data))
  else if action == SECCOMP_RET_TRAP then
    _ ← kbranch .filterCaseTrap true
    -- syscall_rollback: the handler sees the original registers, and the call
    -- returns its number after rt_sigreturn (2.2)
    _ ← forceSigSeccomp nr data false
    skip (.trapped nr data)
  else if action == SECCOMP_RET_TRACE then
    _ ← kbranch .filterCaseTrace true
    if ← kbranch .filterTraceRecheck false then return .proceed
    if ← kbranch .filterTraceNoTracer true then
      -- syscall_set_return_value(current, regs, -ENOSYS, 0)
      skip (.skip errENOSYS)
    else _root_.Leanux.unsupported "SECCOMP_RET_TRACE with a tracer attached (design 9.1)"
  else if action == SECCOMP_RET_USER_NOTIF then
    _ ← kbranch .filterCaseUserNotif true
    _root_.Leanux.unsupported "SECCOMP_RET_USER_NOTIF (design 9.1)"
  else if action == SECCOMP_RET_LOG then
    _ ← kbranch .filterCaseLog true
    seccompLog nr 0 action true
    return .proceed
  else if action == SECCOMP_RET_ALLOW then
    _ ← kbranch .filterCaseAllow true
    return .proceed
  else
    -- KILL_THREAD, KILL_PROCESS and default
    _ ← kbranch .filterCaseKill true
    modifySeccomp fun s => { s with mode := .dead }
    seccompLog nr SIGSYS action true
    -- `action != SECCOMP_RET_KILL_THREAD || (atomic_read(&current->signal->live) == 1)`:
    -- two lines; the task is single-threaded, so `live` is 1
    let coredump ← do
      if ← kbranchCmp .filterKillNotThread (action != SECCOMP_RET_KILL_THREAD) (u32 action) (u32 SECCOMP_RET_KILL_THREAD) then pure true
      else kbranch .filterKillLastThread true
    if coredump then
      -- syscall_rollback; force_sig_seccomp(this_syscall, data, true)
      _ ← forceSigSeccomp nr data true
      return .killed SIGSYS
    _root_.Leanux.invariant "__seccomp_filter: do_exit(SIGSYS) on a thread that is not the last (single-threaded domain)"

/-- __secure_computing_strict (:1059-1077): the do-while over
    `mode1_syscalls`, then `SECCOMP_MODE_DEAD`, the log and `do_exit(SIGKILL)`. -/
def secureComputingStrict (nr : Int) : M FilterOutcome := do
  let table := mode1Syscalls
  for i in [0:table.length] do
    let allowed := table[i]!
    if ← kbranchCmp .strictAllowedMatch (allowed == nr) allowed nr then return .proceed
    let next : Int := if i + 1 < table.length then table[i + 1]! else -1
    if !(← kbranchCmp .strictMoreEntries (next != -1) next (-1)) then break
  modifySeccomp fun s => { s with mode := .dead }
  seccompLog nr SIGKILL SECCOMP_RET_KILL_THREAD true
  -- do_exit(SIGKILL)
  return .killed SIGKILL

/-- __secure_computing (:1378-1404) with `sd = NULL`, for the current task,
    which has a mode (`SYSCALL_WORK_SECCOMP`): the switch on the mode. The
    `PT_SUSPEND_SECCOMP` test is compiled out (`CHECKPOINT_RESTORE` unset). -/
def secureComputing {E : Type} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) : M FilterOutcome := do
  let tk ← getCurrent
  match tk.seccomp.mode with
  | .strict =>
    _ ← kbranch .secureComputingStrict true
    secureComputingStrict nr
  | .filter =>
    _ ← kbranch .secureComputingFilter true
    seccompFilter e nr sd
  | .dead =>
    _ ← kbranch .secureComputingDead true
    _root_.Leanux.invariant "__secure_computing in SECCOMP_MODE_DEAD: a killed task issued a system call"
  | .disabled => _root_.Leanux.invariant "__secure_computing without a mode (the syscall work bit is clear)"

/-! ## Installing: seccomp_prepare_filter, seccomp_attach_filter, the modes (:437-465, :526-531, :661-733, :913-963, :1419-1439, :1947-2044) -/

/-- seccomp_may_assign_mode (:437-445): a mode already set must be the same. -/
def seccompMayAssignMode (mode : SeccompMode) : M Bool := do
  let tk ← getCurrent
  -- `current->seccomp.mode && current->seccomp.mode != seccomp_mode`: one line, compiled per
  -- caller (measured): `(mode & 1) == 0` in the filter caller, `mode != 1` in the strict one
  let cur := tk.seccomp.mode.num
  let cannot := tk.seccomp.mode != .disabled && tk.seccomp.mode != mode
  match mode with
  | .filter => _ ← kbranchCmp .mayAssignModeCmpFilter cannot ((cur &&& 1 : Nat) : Int) 0
  | _ => _ ← kbranchCmp .mayAssignModeCmpStrict cannot cur 1
  if ← kbranch .mayAssignModeSet cannot then
    if ← kbranch .mayAssignModeDiffers true then return false
  return true

/-- seccomp_assign_mode (:449-465): the mode, the mitigation unless
    `SPEC_ALLOW` (`arch_seccomp_spec_mitigate`, a cut: speculation-control
    bits no operation observes), the syscall work bit (the mode gates the
    entry in the mirror). -/
def seccompAssignMode (mode : SeccompMode) (flags : UInt32) : M Unit := do
  modifySeccomp fun s => { s with mode }
  let set := (flags &&& SECCOMP_FILTER_FLAG_SPEC_ALLOW) != 0
  if mode != .strict then   -- the strict caller's constant flags fold the compare
    _ ← kflag .assignModeSpecAllowCmp flags SECCOMP_FILTER_FLAG_SPEC_ALLOW
  if !(← kbranch .assignModeSpecAllow set) then
    pure ()   -- arch_seccomp_spec_mitigate(task): a cut

/-- seccomp_can_sync_threads (:490-524), inlined into seccomp_attach_filter:
    the walk over the thread group validating every other thread. The
    mirror's thread group is the current task alone (design 9.2: a second
    thread is outside the domain), so the walk meets the caller, skips it
    (:503) and returns 0 (:523); the arms for another thread are the C's,
    reached by no run of this representation. -/
def seccompCanSyncThreads : M Int := do
  for _ in [()] do   -- for_each_thread(caller, thread): the group is the caller
    if !(← kbranch .canSyncLoop true) then break
    if ← kbranch .canSyncIsCaller true then continue
    if ← kbranch .canSyncExiting false then continue
    if ← kbranch .canSyncMode false then continue
    _root_.Leanux.unsupported "a second thread in the group (design 9.2)"
  _ ← kbranch .canSyncLoop false
  return 0

/-- seccomp_sync_threads (:597-645), inlined into seccomp_attach_filter:
    the walk that hands every other thread the caller's filter. On the
    one-task group it meets the caller and skips it (:608); nothing changes. -/
def seccompSyncThreads : M Unit := do
  for _ in [()] do
    if !(← kbranch .syncLoop true) then break
    if ← kbranch .syncIsCaller true then continue
    if ← kbranch .syncExiting false then continue
    _root_.Leanux.unsupported "a second thread in the group (design 9.2)"
  _ ← kbranch .syncLoop false

/-- seccomp_attach_filter (:913-963): the path budget over the chain, the
    flags, the chain link, the cache, the head and the count. -/
def seccompAttachFilter (flags : UInt32) (id : FilterId) : M Int := do
  let tk ← getCurrent
  let f ← getFilter id
  let mut total := f.prog.len
  let mut walker := tk.seccomp.filter
  for _ in [0:tk.seccomp.filterCount + 1] do
    if !(← kbranch .attachWalker walker.isSome) then break
    let w ← getFilter walker.get!
    total := total + w.prog.len + 4   -- 4 instr penalty
    walker := w.prev
  if walker.isSome then _root_.Leanux.invariant "seccomp_attach_filter: the chain is longer than filter_count"
  if ← kbranchCmp .attachOverBudget (total > MAX_INSNS_PER_PATH) total MAX_INSNS_PER_PATH then return errENOMEM
  if ← kflag .attachTsync flags SECCOMP_FILTER_FLAG_TSYNC then
    let ret ← seccompCanSyncThreads
    if ← kbranch .attachTsyncFailed (ret != 0) then
      if ← kflag .attachTsyncEsrch flags SECCOMP_FILTER_FLAG_TSYNC_ESRCH then return errESRCH
      else return ret
  if ← kflag .attachLog flags SECCOMP_FILTER_FLAG_LOG then modifyFilter id fun f => { f with log := true }
  if ← kflag .attachWaitKillable flags SECCOMP_FILTER_FLAG_WAIT_KILLABLE_RECV then
    modifyFilter id fun f => { f with waitKillableRecv := true }
  modifyFilter id fun f => { f with prev := tk.seccomp.filter }
  seccompCachePrepare id
  modifySeccomp fun s => { s with filter := some id, filterCount := s.filterCount + 1 }
  if ← kflag .attachTsyncSync flags SECCOMP_FILTER_FLAG_TSYNC then seccompSyncThreads
  return 0

/-- seccomp_filter_free (:526-531) of a prepared filter that was not
    attached: `bpf_prog_destroy` (net/core/filter.c:1466) through
    `__bpf_prog_release` (:1183) and `bpf_release_orig_filter` (:1173), then
    `bpf_prog_free` (kernel/bpf/core.c, a cut) and the `kfree`. -/
def seccompFilterFree (prepared : Option FilterId) : M Unit := do
  if ← kbranch .filterFreeHasFilter prepared.isSome then
    -- bpf_prog_destroy(filter->prog): the type is BPF_PROG_TYPE_UNSPEC (stream U's two
    -- release decisions, shared with bpf_prepare_filter's error arms)
    if ← branch .releaseSocketFilter false then
      _root_.Leanux.invariant "a seccomp program with BPF_PROG_TYPE_SOCKET_FILTER"
    if ← branch .releaseOrigHasFprog true then pure ()   -- kfree(fprog->filter); kfree(fprog)
    -- bpf_prog_free(prog): a cut; kfree(filter)
    modifyK fun k => { k with seccompFilters := k.seccompFilters.erase prepared.get! }

/-- seccomp_prepare_filter (:661-705): the length, the privilege test, the
    allocation, and `bpf_prog_create_from_user` (stream U's) with
    `save_orig` true. On success the filter is in the store with `refs` and
    `users` 1; its allocation identity is the next filter id. -/
def seccompPrepareFilter (fprog : SockFprog) : M (Except Int FilterId) := do
  let tk ← getCurrent
  -- `fprog->len == 0 || fprog->len > BPF_MAXINSNS`: one line, one body; compiled as the
  -- 16-bit unsigned compare `(len - 1) > 0xfff` (measured), carried by the first decision
  if ← kbranchCmp .prepareLenZero (fprog.len == 0 || fprog.len > BPF_MAXINSNS) (minusOneU fprog.len 16) 0xfff then
    return .error errEINVAL
  if ← kbranch .prepareLenOverMax (fprog.len > BPF_MAXINSNS) then return .error errEINVAL
  -- BUG_ON(INT_MAX / fprog->len < sizeof(struct sock_filter)): never, len <= 4096
  -- `!task_no_new_privs(current) && !ns_capable_noaudit(current_user_ns(), CAP_SYS_ADMIN)`: two lines
  if ← kbranch .prepareNoNnp (!tk.noNewPrivs) then
    if ← kbranch .prepareNotCapable (!tk.capSysAdmin) then return .error errEACCES
  if ← kbranch .prepareSfilterNoMem (!(← hiddenAlloc .kzallocSfilter)) then return .error errENOMEM
  let id := (← getK).nextFilter
  modifyK fun k => { k with nextFilter := k.nextFilter + 1 }
  -- mutex_init(&sfilter->notify_lock): the notifier is not mirrored
  match ← bpfProgCreateFromUser fprog with
  | .error e =>
    _ ← kbranchCmp .prepareCreateErr true e 0
    return .error e   -- kfree(sfilter)
  | .ok prog =>
    _ ← kbranchCmp .prepareCreateErr false 0 0
    -- refcount_set(&sfilter->refs, 1); refcount_set(&sfilter->users, 1); init_waitqueue_head
    let flt : SeccompFilter := { id, refs := 1, users := 1, prog := prog.toKernel,
                                 origProg := prog.origProg.map SockFilter.toKernel }
    modifyK fun k => { k with seccompFilters := k.seccompFilters.insert id flt }
    return .ok id

/-- seccomp_prepare_user_filter (:714-733): the `copy_from_user` of the
    `sock_fprog` (`-EFAULT` for an unmapped pointer, op 30's `bad: fprog`),
    then `seccomp_prepare_filter`. -/
def seccompPrepareUserFilter (fprog : SockFprog) (badFprog : Bool) : M (Except Int FilterId) := do
  if ← kbranch .userFilterCopyFault badFprog then return .error errEFAULT
  seccompPrepareFilter fprog

/-- has_duplicate_listener (:1917-1925): the new filter has no notifier. -/
def hasDuplicateListener : M Bool := do
  if ← kbranch .dupListenerNoNotif true then return false
  _root_.Leanux.unsupported "a filter with a notifier (NEW_LISTENER)"

/-- seccomp_set_mode_filter (:1947-2044). `NEW_LISTENER` leaves the domain
    at its first test after the prepare (design 9.1); `TSYNC` on the one-task
    group takes the C's path (the cred_guard_mutex uncontended, the two thread
    walks meeting only the caller). -/
def seccompSetModeFilter (flags : UInt32) (fprog : SockFprog) (badFprog : Bool) : M Int := do
  -- `flags & ~SECCOMP_FILTER_FLAG_MASK`: compiled as the unsigned `flags > MASK` (measured)
  if ← kbranchCmp .setFilterBadFlags (flags > SECCOMP_FILTER_FLAG_MASK) flags.toNat SECCOMP_FILTER_FLAG_MASK.toNat then
    return errEINVAL
  -- `TSYNC && NEW_LISTENER && !TSYNC_ESRCH` over three lines: one compiled test
  -- `(flags & 0x19) == 9` (measured), carried by the first decision, the other two plain
  let three := SECCOMP_FILTER_FLAG_TSYNC ||| SECCOMP_FILTER_FLAG_NEW_LISTENER ||| SECCOMP_FILTER_FLAG_TSYNC_ESRCH
  let both := SECCOMP_FILTER_FLAG_TSYNC ||| SECCOMP_FILTER_FLAG_NEW_LISTENER
  if ← kbranchCmp .setFilterTsync ((flags &&& three) == both) (flags &&& three).toNat both.toNat then
    if ← kbranch .setFilterNewListener true then
      if !(← kbranch .setFilterTsyncEsrch false) then return errEINVAL
  -- `WAIT_KILLABLE_RECV && !NEW_LISTENER` over two lines: one compiled test
  -- `(flags & 0x28) == 0x20` (measured), carried by the first decision
  let pair := SECCOMP_FILTER_FLAG_WAIT_KILLABLE_RECV ||| SECCOMP_FILTER_FLAG_NEW_LISTENER
  if ← kbranchCmp .setFilterWaitKillable ((flags &&& pair) == SECCOMP_FILTER_FLAG_WAIT_KILLABLE_RECV)
      (flags &&& pair).toNat SECCOMP_FILTER_FLAG_WAIT_KILLABLE_RECV.toNat then
    if !(← kbranch .setFilterWaitNewListener false) then return errEINVAL
  let id ← match ← seccompPrepareUserFilter fprog badFprog with
    | .error e =>
      _ ← kbranch .setFilterPrepareErr true
      return e
    | .ok id =>
      _ ← kbranch .setFilterPrepareErr false
      pure id
  if ← kflag .setFilterNewListenerFlag flags SECCOMP_FILTER_FLAG_NEW_LISTENER then
    _root_.Leanux.unsupported "SECCOMP_FILTER_FLAG_NEW_LISTENER (design 9.1)"
  -- `flags & TSYNC && mutex_lock_killable(&cred_guard_mutex)`
  if ← kflag .setFilterTsyncLock flags SECCOMP_FILTER_FLAG_TSYNC then
    -- mutex_lock_killable(&current->signal->cred_guard_mutex): uncontended on
    -- one task, it returns 0; its killable arm needs a pending fatal signal
    if ← kbranch .setFilterTsyncLockFailed false then
      _root_.Leanux.unsupported "mutex_lock_killable(cred_guard_mutex) interrupted by a fatal signal"
  -- spin_lock_irq(&current->sighand->siglock)
  let mut ret : Int := errEINVAL
  let mut prepared : Option FilterId := some id
  if ← kbranch .setFilterCannotAssign (!(← seccompMayAssignMode .filter)) then
    pure ()   -- goto out
  else if ← kbranch .setFilterDuplicateListener (← hasDuplicateListener) then
    ret := errEBUSY
  else
    ret ← seccompAttachFilter flags id
    if ← kbranch .setFilterAttachErr (ret != 0) then
      pure ()   -- goto out
    else
      prepared := none   -- do not free the successfully attached filter
      seccompAssignMode .filter flags
  -- out: spin_unlock_irq
  if ← kflag .setFilterTsyncUnlock flags SECCOMP_FILTER_FLAG_TSYNC then
    pure ()   -- mutex_unlock(&current->signal->cred_guard_mutex): a cut
  -- out_put_fd
  if ← kflag .setFilterNewListenerOut flags SECCOMP_FILTER_FLAG_NEW_LISTENER then
    _root_.Leanux.invariant "NEW_LISTENER reached out_put_fd: its arm leaves the domain first"
  -- out_free
  seccompFilterFree prepared
  return ret

/-- seccomp_set_mode_strict (:1419-1439); `disable_TSC` is a cut. -/
def seccompSetModeStrict : M Int := do
  if ← kbranch .setStrictCannotAssign (!(← seccompMayAssignMode .strict)) then return errEINVAL
  seccompAssignMode .strict 0
  return 0

/-- seccomp_get_action_avail (:2053-2075): the `u32` is copied from a valid
    pointer (op 34 has no `bad` form); the eight known actions answer 0. -/
def seccompGetActionAvail (action : UInt32) : M Int := do
  if ← kbranch .actionAvailCopyFault false then return errEFAULT
  let known := [SECCOMP_RET_KILL_PROCESS, SECCOMP_RET_KILL_THREAD, SECCOMP_RET_TRAP, SECCOMP_RET_ERRNO,
                SECCOMP_RET_USER_NOTIF, SECCOMP_RET_TRACE, SECCOMP_RET_LOG, SECCOMP_RET_ALLOW]
  if ← kbranch .actionAvailKnown (known.contains action) then return 0
  return errEOPNOTSUPP

/-- seccomp_get_notif_sizes (:2077-2089): the three sizes are copied out. -/
def seccompGetNotifSizes : M Int := do
  if ← kbranch .notifSizesCopyFault false then return errEFAULT
  return 0

/-- The `uargs` of `do_seccomp`: NULL, a `sock_fprog` (good or unmapped), a
    `u32` action, or the sizes buffer. -/
inductive SeccompArgs where
  | null
  | fprog (fprog : SockFprog) (bad : Bool)
  | action (action : UInt32)
  | sizes
  deriving Repr

/-- do_seccomp (:2092-2115), the common entry of `seccomp(2)` and `prctl`. -/
def doSeccomp (op : Nat) (flags : UInt32) (uargs : SeccompArgs) : M Int := do
  if op == SECCOMP_SET_MODE_STRICT then
    _ ← kbranch .doSeccompCaseStrict true
    -- `flags != 0 || uargs != NULL`: one line, one body; no comparison recorded (measured)
    if ← kbranch .doSeccompStrictFlags (flags != 0) then return errEINVAL
    let nonNull := match uargs with | .null => false | _ => true
    if ← kbranch .doSeccompStrictArgs nonNull then return errEINVAL
    seccompSetModeStrict
  else if op == SECCOMP_SET_MODE_FILTER then
    _ ← kbranch .doSeccompCaseFilter true
    match uargs with
    | .fprog fprog bad => seccompSetModeFilter flags fprog bad
    | .null =>
      -- a NULL `sock_fprog *` faults at seccomp_prepare_user_filter's copy
      seccompSetModeFilter flags { len := 0, filter := none } true
    | _ => _root_.Leanux.invariant "SECCOMP_SET_MODE_FILTER with a non-fprog argument"
  else if op == SECCOMP_GET_ACTION_AVAIL then
    _ ← kbranch .doSeccompCaseActionAvail true
    if ← kbranchCmp .doSeccompActionAvailFlags (flags != 0) flags.toNat 0 then return errEINVAL
    match uargs with
    | .action a => seccompGetActionAvail a
    | _ => _root_.Leanux.invariant "SECCOMP_GET_ACTION_AVAIL without an action"
  else if op == SECCOMP_GET_NOTIF_SIZES then
    _ ← kbranch .doSeccompCaseNotifSizes true
    if ← kbranchCmp .doSeccompNotifSizesFlags (flags != 0) flags.toNat 0 then return errEINVAL
    seccompGetNotifSizes
  else
    _ ← kbranch .doSeccompCaseDefault true
    return errEINVAL

/-- prctl_set_seccomp (:2130-2155): mode 1 is strict with a NULL argument,
    mode 2 is filter, anything else `-EINVAL`; flags are always zero. -/
def prctlSetSeccomp (mode : Nat) (filter : SeccompArgs) : M Int := do
  if mode == 1 then
    _ ← kbranch .prctlSetCaseStrict true
    doSeccomp SECCOMP_SET_MODE_STRICT 0 .null
  else if mode == 2 then
    _ ← kbranch .prctlSetCaseFilter true
    doSeccomp SECCOMP_SET_MODE_FILTER 0 filter
  else
    _ ← kbranch .prctlSetCaseDefault true
    return errEINVAL

/-- prctl_get_seccomp (:1407-1410): the mode, no branch. -/
def prctlGetSeccomp : M Int := do
  return (← getCurrent).seccomp.mode.num

/-! ## The parent's clone: get_seccomp_filter (:971-980) -/

/-- get_seccomp_filter(current), from `copy_seccomp` (kernel/fork.c, an
    unlisted file) in the parent's window: one `refs` and one `users`
    increment on the head filter. -/
def getSeccompFilter (t : TaskRef) : M Unit := do
  let tk ← getTask t
  if ← kbranch .getFilterNone tk.seccomp.filter.isNone then return
  let id := tk.seccomp.filter.get!
  let f ← getFilter id
  refcountInc f.refs   -- __get_seccomp_filter: refcount_inc(&filter->refs)
  modifyFilter id fun f => { f with refs := f.refs + 1 }
  let f ← getFilter id
  refcountInc f.users   -- refcount_inc(&orig->users)
  modifyFilter id fun f => { f with users := f.users + 1 }

end Leanux.Seccomp
