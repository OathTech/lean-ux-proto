import Leanux.Seccomp.Filter
import Leanux.Env

/-!
# The five seccomp operations (docs/2026-10-12-seccomp-design.md, 6.1, 6.2)

seccomp stream V. `seccomp_install` (30) is `seccomp(SECCOMP_SET_MODE_FILTER,
flags, &fprog)` or `prctl(PR_SET_SECCOMP, 2, &fprog)`; `seccomp_probe` (31)
is one call of the probe set, in the trace process or in a sandboxed child
(the fork, the child's optional strict call, its probe, its exit and the
parent's `wait4`, each through `__secure_computing` once a mode is set);
`seccomp_prctl` (32) and `seccomp_capdrop` (33) are data-only (6.3:
`kernel/sys.c` and `kernel/capability.c` are not anchored); `seccomp_query`
(34) is `seccomp(SECCOMP_GET_ACTION_AVAIL | GET_NOTIF_SIZES, flags, ...)`.

The self-sandboxing rule (6.2 rule 1): every number outside the probe set
is constantly allowed by the chain, so the harness's own calls take the
cache path; a chain the kernel accepted but the rule did not hold for stops
the mirror with `invariant`. The engine is `MiniInterp` (4.4).
-/

namespace Leanux.Seccomp
open Lean

inductive InstallVia where
  | seccomp | prctl
  deriving Repr, BEq, DecidableEq

/-- Op 30's `bad`: the `sock_fprog` pointer or the instruction pointer is unmapped. -/
inductive BadPtr where
  | none | fprog | insns
  deriving Repr, BEq, DecidableEq

inductive ProbeWhere where
  | self | child
  deriving Repr, BEq, DecidableEq

inductive StrictVia where
  | seccomp | prctl
  deriving Repr, BEq, DecidableEq

inductive PrctlCmd where
  | setNoNewPrivs | getNoNewPrivs | getSeccomp
  deriving Repr, BEq, DecidableEq

inductive QueryCmd where
  | getActionAvail | getNotifSizes
  deriving Repr, BEq, DecidableEq

/-- x86-64 system call numbers the operations and the harness make. -/
def NR_rt_sigreturn : Int := 15
def NR_wait4 : Int := 61
def NR_capset : Int := 126
def NR_prctl : Int := 157
def NR_seccomp : Int := 317

/-- The probe set (6.2 rule 1): getuid, getgid, geteuid, getegid, 1000 (out
    of range), uretprobe 335. -/
def probeSet : List Int := [102, 104, 107, 108, 1000, NR_URETPROBE]

def zeroArgs : Array UInt64 := #[0, 0, 0, 0, 0, 0]

/-- `struct seccomp_data` for a call of the current task: the number, the
    architecture, the arguments; `instruction_pointer` is not a hidden input
    (3.2), so `ip` is `none`. -/
def seccompData (nr : Int) (args : Array UInt64 := zeroArgs) : SeccompData :=
  { nr, arch := AUDIT_ARCH_X86_64, args }

/-- The entry of a system call of the current task: `__secure_computing`
    once a mode is set (`SYSCALL_WORK_SECCOMP`), nothing before. -/
def enterSyscall (nr : Int) (args : Array UInt64 := zeroArgs) : M FilterOutcome := do
  let tk ← getCurrent
  if tk.seccomp.mode == .disabled then return .proceed
  secureComputing MiniInterp.mk nr (seccompData nr args)

/-- A harness call of the trace process (every number outside the probe
    set, 6.2 rule 1): by the rule it is a cache hit, so its arguments are
    never read. A chain that does not constantly allow it is a trace outside
    the domain by construction (the guest ran an unverified filter on
    itself): `invariant`. -/
def enterHarnessCall (nr : Int) : M Unit := do
  let tk ← getCurrent
  match tk.seccomp.mode with
  | .disabled => return
  | .filter =>
    match tk.seccomp.filter with
    | none => _root_.Leanux.invariant "SECCOMP_MODE_FILTER without a filter"
    | some id =>
      let head ← getFilter id
      if !(nr ≥ 0 && nr < NR_syscalls && head.allowNative.getLsbD nr.toNat) then
        _root_.Leanux.invariant s!"harness call {nr} is not const-allowed by the chain (design 6.2 rule 1)"
      match ← secureComputing MiniInterp.mk nr (seccompData nr) with
      | .proceed => return
      | _ => _root_.Leanux.invariant s!"harness call {nr} did not proceed through the cache"
  | .strict => _root_.Leanux.invariant "a harness call of the trace process under strict mode (child-only, design 6.2)"
  | .dead => _root_.Leanux.invariant "a harness call of a killed task"

/-- The probe set's results as root: 0 for the four ids, `-ENOSYS` for 1000
    (outside the table) and for uretprobe (`UPROBES` absent, 2.6). -/
def probeResult (nr : Int) : M Int := do
  if [102, 104, 107, 108].contains nr then return 0
  if nr == 1000 || nr == NR_URETPROBE then return errENOSYS
  _root_.Leanux.unsupported s!"probe {nr} outside the probe set (design 6.2 rule 1)"

/-- After a `TRAP`: the `SIGSYS` is delivered to the handler on the return to
    user mode (an environment effect, 2.2), the handler records the three
    fields and returns through `rt_sigreturn`, whose entry runs the filter
    (a cache hit by the rule), and the call returns its own number (2.2). -/
def trapReturn (nr _data : Int) : M Int := do
  Env.trapDelivered
  enterHarnessCall NR_rt_sigreturn
  return nr

/-- The handler's record of a `TRAP` in the trace process (6.1: `sigsys`). -/
def sigsysRecord (nr data : Int) : Json :=
  Json.mkObj [("nr", toJson nr), ("data", toJson data), ("arch", toJson AUDIT_ARCH_X86_64.toNat)]

/-- The probe's two observation fields (contract: `sigsys` null unless a
    `TRAP` was caught, `child` null for a self probe). -/
def probeOut (sigsys : Json) (child : Json) : M Unit :=
  modify fun w => { w with extraOut := w.extraOut ++ [("sigsys", sigsys), ("child", child)] }

/-- Op 31 in the trace process. A killing chain is kept out of `self` by the
    validator; the mirror would have no task to continue with. -/
def sysSeccompProbeSelf (nr : Int) (args : Array UInt64) : M Int := do
  match ← enterSyscall nr args with
  | .proceed =>
    probeOut .null .null
    probeResult nr
  | .skip r =>
    probeOut .null .null
    return r
  | .trapped nr' data =>
    probeOut (sigsysRecord nr' data) .null
    trapReturn nr' data
  | .killed sig =>
    _root_.Leanux.invariant s!"the trace process was killed by its filter (signal {sig}; the validator keeps kills in a child)"

/-- `exit` (60), the one probe outside the probe set, for a strict child
    (contract): the call ends the child with `args[0]` as its status. -/
def NR_exit : Int := 60

/-- Op 31 in a sandboxed child (6.2 rule 2). In the parent's window: glibc's
    `fork` (`Env.forkCalls`), `copy_process`'s clocks, `copy_seccomp`'s
    `get_seccomp_filter`, the child's creation; in the child's window: its
    optional strict call, the probe, its exit call; then the parent's
    `wait4`. The child's exit runs `seccomp_filter_release` outside every
    window (2.8): the environment effect `Env.childExit`. -/
def sysSeccompProbeChild (nr : Int) (args : Array UInt64) (strict : Option StrictVia) : M Int := do
  for c in Env.forkCalls do enterHarnessCall c
  Env.forkClocks
  getSeccompFilter .task
  Env.childCreate
  modifyK fun k => { k with current := .child }
  let mut record : List (String × Json) := []
  let mut alive := true
  if let some via := strict then
    let (nrCall, run) : Int × M Int := match via with
      | .seccomp => (NR_seccomp, doSeccomp SECCOMP_SET_MODE_STRICT 0 .null)
      | .prctl => (NR_prctl, prctlSetSeccomp 1 .null)
    match ← enterSyscall nrCall with
    | .proceed => record := record ++ [("strict_ret", toJson (← run))]
    | .skip r => record := record ++ [("strict_ret", toJson r)]
    | .trapped n d => record := record ++ [("strict_ret", toJson (← trapReturn n d))]
    | .killed sig =>
      alive := false
      record := record ++ [("signal", toJson sig)]
  let mut ret : Int := 0
  let mut exited := false
  let mut sigsys : Json := .null
  if alive then
    match ← enterSyscall nr args with
    | .proceed =>
      if nr == NR_exit then
        -- the probe is the exit: the child leaves without writing (`exited`)
        exited := true
        record := record ++ [("exited", toJson ((args.getD 0 0).toNat % 256))]
      else ret ← probeResult nr
    | .skip r => ret := r
    | .trapped n d =>
      -- the handler is the parent's copy (2.8); its record reaches the parent
      -- through the shared page (the contract)
      sigsys := sigsysRecord n d
      ret ← trapReturn n d
    | .killed sig =>
      alive := false
      record := record ++ [("signal", toJson sig)]
  if alive && !exited then
    -- the child writes `ret` into the shared page (memory), then leaves
    let exitNr := Env.childExitCall strict.isSome
    match ← enterSyscall exitNr with
    | .proceed => record := record ++ [("ret", toJson ret)]
    | .killed sig => record := record ++ [("signal", toJson sig)]
    | .skip _ | .trapped .. =>
      _root_.Leanux.invariant s!"the child's exit call {exitNr} is not const-allowed (design 6.2 rule 1)"
  Env.childExit
  modifyK fun k => { k with current := .task }
  enterHarnessCall NR_wait4
  Env.childDrop
  probeOut sigsys (Json.mkObj record)
  return 0

/-- Op 30. `len` overrides the program's length (the length arms); `bad`
    names an unmapped pointer (the two `-EFAULT` arms). -/
def sysSeccompInstall (via : InstallVia) (flags : UInt32) (filter : Option _root_.Leanux.ClassicProg)
    (len : Option Nat) (bad : BadPtr) (mode : Nat) : M Int := do
  let fprog : SockFprog := { len := len.getD ((filter.map (·.size)).getD 0),
                             filter := filter.map (·.map SockFilter.ofKernel), insnsFault := bad == .insns }
  let args := SeccompArgs.fprog fprog (bad == .fprog)
  match via with
  | .seccomp => doSeccomp SECCOMP_SET_MODE_FILTER flags args
  | .prctl =>
    if flags != 0 then _root_.Leanux.unsupported "flags with the prctl install (prctl passes none)"
    prctlSetSeccomp mode args

/-- Op 32, data-only (6.3): `PR_SET_NO_NEW_PRIVS` (kernel/sys.c:2632-2636),
    `PR_GET_NO_NEW_PRIVS` (:2638-2641), `PR_GET_SECCOMP` (:2548). `args` is
    `arg2..arg5`. -/
def sysSeccompPrctl (cmd : PrctlCmd) (args : Array UInt64) : M Int := do
  let a (i : Nat) : UInt64 := args.getD i 0
  let t := (← getK).current
  match cmd with
  | .setNoNewPrivs =>
    if a 0 != 1 || a 1 != 0 || a 2 != 0 || a 3 != 0 then return errEINVAL
    modifyTask t fun tk => { tk with noNewPrivs := true }
    return 0
  | .getNoNewPrivs =>
    if a 0 != 0 || a 1 != 0 || a 2 != 0 || a 3 != 0 then return errEINVAL
    return if (← getTask t).noNewPrivs then 1 else 0
  | .getSeccomp => prctlGetSeccomp

/-- Op 33, data-only: `capset` without `CAP_SYS_ADMIN` in the effective,
    permitted and inheritable sets. -/
def sysSeccompCapdrop : M Int := do
  let t := (← getK).current
  modifyTask t fun tk => { tk with capSysAdmin := false }
  return 0

/-- Op 34. -/
def sysSeccompQuery (cmd : QueryCmd) (action flags : UInt32) : M Int :=
  match cmd with
  | .getActionAvail => doSeccomp SECCOMP_GET_ACTION_AVAIL flags (.action action)
  | .getNotifSizes => doSeccomp SECCOMP_GET_NOTIF_SIZES flags .sizes

end Leanux.Seccomp
