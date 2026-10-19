# seccomp over a single task — design v2, 2026-10-12

[AGENT, fork of the coordinator] A design, not a build: no mirror, guest or
kernel code is written here. It follows the kernel scout's profile
(`docs/2026-10-12-kernel-scout.md`, 4.4), the simulation-target review's
rules for cuts and stops (`docs/2026-10-12-simulation-target-review.md`, 3.2
and 4.4), the user's seam of 2026-10-12 (`docs/decisions.md`: the eBPF
engine below `seccomp_run_filters` is a service with a stated ISA contract,
never anchored; the user's separate eBPF JIT project owns that seam) and the
interface allocations on `task/next-targets` (`docs/2026-10-11-interface.md`:
opcodes 30-34, HiddenSite ids 400-419 (moved from 200-219 by the interface
commit: that block is `Worker.sectionId`'s from index 15), config
`SECCOMP`/`SECCOMP_FILTER`).
Every kernel claim below was read in the configured source, `.deps/linux`
(6.12.110), with the line numbers given; none has been run against a build,
and the current oracle has `CONFIG_SECCOMP` unset, so section 11's step 0 is
a measurement on a local build.

This is v2: the independent audit (section 14) found three things the first
draft would have failed on at the first child probe, the first `TRAP` and the
first `prctl`, and a dozen smaller corrections. Each is fixed where it stands;
section 15 lists them against the audit's numbering; section 16 is the one
case that goes to the user.

The scout's profile needs one addition (section 6.2): a filter installed in
the trace process governs the trace process's own system calls, so the
harness's calls must be allowed by construction, and a kill can only be
observed from outside the killed task.

## 1. Target

Mirror seccomp as the C does it, in one task, with no second thread, no
tracer and no listener:

- installing a filter with `seccomp(SECCOMP_SET_MODE_FILTER, flags, &fprog)`
  and with `prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &fprog)`, with every
  check the C makes on the way: the no-new-privs or `CAP_SYS_ADMIN`
  precondition, the classic BPF checker, seccomp's own load rewriting, the
  translation to eBPF, the per-path instruction budget, the action cache;
- strict mode (`SECCOMP_SET_MODE_STRICT`, `PR_SET_SECCOMP` mode 1), in a
  sandboxed child only (6.2);
- chains: a second and third filter on the same task, the most-restrictive
  rule across the chain, the cache's monotone bitmap;
- the actions as a single task observes them: `ALLOW`, `ERRNO` (with the
  `MAX_ERRNO` cap), `LOG`, `TRAP` (through a `SIGSYS` handler),
  `KILL_THREAD` and `KILL_PROCESS` (through a sandboxed child's wait
  status), a non-canonical action (the `default` arm), and `TRACE` without
  a tracer (its `-ENOSYS` arm);
- the signal generation those actions run: `force_sig_info_to_task` and the
  wake arm of `complete_signal`, an extension of the pipes' signal mirror
  (2.2, 4.5) that widens the P design's decision P9 (section 16);
- the companions: `PR_SET_NO_NEW_PRIVS`, `PR_GET_NO_NEW_PRIVS`,
  `PR_GET_SECCOMP`, `SECCOMP_GET_ACTION_AVAIL`, `SECCOMP_GET_NOTIF_SIZES`,
  and a capability drop so the `-EACCES` arm is reachable;
- the filter's inheritance across `fork`, witnessed in the parent's `clone`;
  its release at the child's exit is an environment effect (2.8, 6.2).

What this adds to the mirror beyond seccomp's own control flow is a
**program checker and translator** (`net/core/filter.c`'s classic BPF
checker and its conversion to eBPF) mirrored with full control-flow
correspondence, and an **engine seam**: the one call that runs the
translated program, `bpf_prog_run_pin_on_cpu` at `kernel/seccomp.c:426`, is
a service with a stated contract (4.4). The mirror ships a minimal
interpreter for the opcode subset the translation emits so that it is
executable today; an external Lean model of the eBPF ISA can replace it
without touching the rest.

The feature, named at the altitude the evidence supports (pre-release review
finding 11, 2026-10-14): **single-task seccomp with classic-BPF translation
and an interpreter service**. Out of scope, fail-noisy (section 9):
`NEW_LISTENER` and `USER_NOTIF` (the listener protocol), `TRACE` with a
tracer (the ptrace protocol), a second thread (so threaded `TSYNC`
synchronisation), strict mode in the trace process. In scope since the
review: `TSYNC` on the one-task group (the C's no-op path, 2.4) and filters
that read the instruction pointer (recorded at its source, 3.2).

## 2. The kernel paths, verified

Configuration facts the paths depend on (`kernel/config-x86_64-net-choice`):
`CONFIG_HAVE_ARCH_SECCOMP=y`, `CONFIG_HAVE_ARCH_SECCOMP_FILTER=y`, `SECCOMP`
unset (:465-467); `CONFIG_BPF=y` (:99), `BPF_SYSCALL` and `BPF_JIT` unset
(:106-107); `AUDIT` unset (:60); `CHECKPOINT_RESTORE` unset (:162);
`IA32_EMULATION` unset (:399), so `CONFIG_COMPAT` is off; `COREDUMP=y`
(:597); `PROC_SYSCTL=y` (:1533); `UPROBES` absent, so `uprobes.o` is not
built (`arch/x86/kernel/Makefile:154`) and `uretprobe` is a `COND_SYSCALL`
(`kernel/sys_ni.c:394`) answering `-ENOSYS`. On x86-64 `SECCOMP_ARCH_NATIVE`
is `AUDIT_ARCH_X86_64`, `SECCOMP_ARCH_NATIVE_NR` is `NR_syscalls` (463 in the
built headers, `__NR_syscalls`; `mseal` 462 is the last entry), and
`SECCOMP_ARCH_COMPAT` is undefined (`arch/x86/include/asm/seccomp.h`).
`__NR_uretprobe` is 335; there is no `uprobe` call on this branch.

### 2.1 Entry: `__secure_computing` (:1378-1404)

Once a mode is assigned, `seccomp_assign_mode` (:449-465) sets
`SYSCALL_WORK_SECCOMP`; from then on every system call of the task takes
the slow entry path, `syscall_trace_enter` (`kernel/entry/common.c:28-75`),
which calls `__secure_computing(NULL)` at :54-58 and skips the call when it
returns -1. `kernel/entry` is not instrumented (`kernel/entry/Makefile:7`),
so the first witnessed function is `__secure_computing` itself. The
`PT_SUSPEND_SECCOMP` test is compiled out (`CHECKPOINT_RESTORE` unset).
`this_syscall` comes from `syscall_get_nr`; the switch on `mode` has three
live arms: strict (2.9), filter (2.2), and `SECCOMP_MODE_DEAD`, which is
unreachable in this domain (a killed task never returns to issue a call)
and is an `invariant` stop in the mirror.

### 2.2 The filtered call: `__seccomp_filter` (:1244-1366)

`populate_seccomp_data` (:246-266) fills `nr`, `arch`
(`AUDIT_ARCH_X86_64`), the six arguments and `instruction_pointer`
(`KSTK_EIP`). `seccomp_run_filters` (:406-434) returns the composed result;
`data = ret & 0xffff`, `action = ret & 0xffff0000`. The arms:

- `ERRNO` (:1268-1274): `data` capped at `MAX_ERRNO` (4095), the return
  value set to `-data` (`syscall_set_return_value`,
  `arch/x86/include/asm/syscall.h:72-77`: `regs->ax = error`), `goto skip`.
  Data 0 returns 0 with no error.
- `TRAP` (:1276-1281): `syscall_rollback` (`syscall.h:41-45`: `regs->ax =
  regs->orig_ax`, i.e. the register holds the call number), then
  `force_sig_seccomp(nr, data, false)` (`kernel/signal.c:1855-1868`:
  `SIGSYS`, `si_code = SYS_SECCOMP`, `si_errno = data`, `si_syscall = nr`,
  `si_arch`, `HANDLER_CURRENT`), `goto skip`. With a handler installed the
  task survives and the call returns `nr` in `rax` after `rt_sigreturn`.
- `TRACE` (:1283-1324): with no tracer, `ptrace_event_enabled` is false and
  the return value is set to `-ENOSYS`, `goto skip`. The tracer arm and the
  `recheck_after_trace` re-entry are out of scope (9.2).
- `USER_NOTIF` (:1326-1330): out of scope (9.2).
- `LOG` (:1332-1334): `seccomp_log(nr, 0, action, true)`, return 0 (the
  call proceeds).
- `ALLOW` (:1336-1342): return 0; `match` is NULL here by construction.
- `KILL_THREAD`, `KILL_PROCESS` and `default` (:1344-1359): the mode becomes
  `SECCOMP_MODE_DEAD`; `seccomp_log(nr, SIGSYS, action, true)`; then, since
  the action is not `KILL_THREAD` or the thread is the last one alive (both
  true in a single-threaded task), `syscall_rollback` and
  `force_sig_seccomp(nr, data, true)` (`HANDLER_EXIT`: the signal cannot
  be caught; the task dies with `SIGSYS`). The `else do_exit(SIGSYS)` arm
  is unreachable in this domain and is an `invariant` stop.
- `skip` (:1364-1366): `seccomp_log(nr, 0, action, match ? match->log :
  false)`, return -1.

`seccomp_log` (:1000-1041) switches on the action and consults
`seccomp_actions_logged` (:992, default: every action but `ALLOW`); its
only effect is `audit_seccomp`, an empty inline with `AUDIT` unset
(`include/linux/audit.h:620-621`). The decisions are mirrored; the effect
is nothing.

**The signal chain.** `force_sig_seccomp` enters `force_sig_info_to_task`
(`kernel/signal.c:1328-1363`), and from there the chain the pipes mirror
already anchors for `SIGPIPE` (`Leanux/Kernel/Signal.lean`; P design
decision P9): `send_signal_locked` (:1214) → `__send_signal_locked`
(:1073-1188) with `prepare_signal` (:902-967), `legacy_queue`,
`__sigqueue_alloc` (:404-442; `override_rlimit` holds because `si_code` is
`SYS_SECCOMP`, non-negative), the `copy_siginfo` of a real siginfo,
`sigaddset`, `complete_signal` (:994-1066). The pipes mirror stops
`unsupported` on every arm an unblocked signal takes (`Signal.lean:23-26`,
`:110`, `:115`, `:142`); `SIGSYS` here is unblocked with a handler (`TRAP`)
or fatal (`KILL`), so the design extends the mirror (4.5) along exactly
these lines, read in the source:

- `force_sig_info_to_task`: `ignored` and `blocked` are false in this
  domain; `handler != HANDLER_CURRENT` is the `KILL` case, which forces
  `SIG_DFL` and sets `SA_IMMUTABLE`; `SIG_DFL && !ptrace` clears
  `SIGNAL_UNKILLABLE`; after `send_signal_locked`, the `!task_sigpending`
  test is false because `complete_signal` already woke the task, so the
  second `signal_wake_up` is skipped.
- `prepare_signal`: `SIGSYS` is neither stop nor continue; `sig_ignored` is
  false with a handler or with the forced default.
- `complete_signal`: `wants_signal` (:977-992) is true (not blocked, not
  `PF_EXITING`, not `SIGKILL`, not stopped, `task_curr`), so `t = p`;
  `sig_fatal` (`include/linux/signal.h:451`) is false with a handler and
  true with the forced default; in the fatal case `core_state ||
  !SIGNAL_GROUP_EXIT`, `!real_blocked` and `!ptrace` hold and
  `sig_kernel_coredump(SIGSYS)` is true, so the group-exit block is
  skipped; then `signal_wake_up(t, sig == SIGKILL)` →
  `signal_wake_up_state` (:759-774): `TIF_SIGPENDING`, and `wake_up_state`
  on a running task, which is a cut.

Delivery is not anchored: `get_signal`, `dequeue_signal`, the handler frame
and `rt_sigreturn`'s `set_current_blocked` are unlisted functions of a
listed file, tolerated by the check unless they cover a span line of a
listed decision (`evaluator/check.py:868`). Their data effect on the task
is an environment effect of the `TRAP` outcome: `SIGSYS` leaves the pending
set, `blocked` is as before once the handler returns, the flag clears.
Step 0 measures one `TRAP` trace for span-line collisions; a collision is
modelled or declared in `known_gaps`, never absorbed. For a kill in the
child, `get_signal`'s fatal arm, `do_coredump` (`fs/coredump.c:704`:
`RLIMIT_CORE` zero fails the limit test, so no file and no `0x80` in the
wait status, `coredump_finish` :465-472) and `do_group_exit` run in the
child's window; the first two are unlisted files.

### 2.3 The chain and the cache: `seccomp_run_filters` (:406-434)

`ret` starts at `ALLOW`; `f` is `current->seccomp.filter`, the most
recently attached filter. The `WARN_ON(f == NULL)` arm returns
`KILL_PROCESS` and is an `invariant` stop. `seccomp_cache_check_allow`
(:369-394, native-only branch) tests `nr` against the head filter's
`allow_native` bitmap through `seccomp_cache_check_allow_bitmap`
(:351-360): a number outside `0..462` is never cached. A hit returns
`ALLOW` without running anything. Otherwise the loop runs every filter
through `bpf_prog_run_pin_on_cpu(f->prog, sd)` (:426, the engine seam,
4.4) and keeps the result whose `ACTION_ONLY` (:396, the upper 16 bits as
a signed 32-bit value) is strictly smaller, recording the filter in
`*match`. So `KILL_PROCESS` (0x80000000, negative) beats everything,
`KILL_THREAD` (0) beats `TRAP` (0x30000), which beats `ERRNO` (0x50000),
`USER_NOTIF`, `TRACE`, `LOG`, `ALLOW` (0x7fff0000); ties go to the newest
filter; the data bits of the winner are what `__seccomp_filter` sees.

### 2.4 Installing a filter: `seccomp_set_mode_filter` (:1947-2044)

In order: the flag mask (:1957, `-EINVAL`); `TSYNC` with `NEW_LISTENER`
without `TSYNC_ESRCH` (:1967-1970); `WAIT_KILLABLE_RECV` without
`NEW_LISTENER` (:1976-1978); then `seccomp_prepare_user_filter` (:714-733:
`copy_from_user` of the `sock_fprog`, `-EFAULT` on a bad pointer) and
`seccomp_prepare_filter` (:661-705):

1. `fprog->len == 0 || > BPF_MAXINSNS` (4096): `-EINVAL` (:672).
2. the precondition (:683-685): the task has no-new-privs or
   `ns_capable_noaudit(CAP_SYS_ADMIN)`; otherwise `-EACCES`. The guest runs
   as root, so the second disjunct holds until the trace drops the
   capability (6.1, op 33).
3. `kzalloc` of the `seccomp_filter` (:688; `-ENOMEM`).
4. `bpf_prog_create_from_user(&prog, fprog, seccomp_check_filter, true)`
   (:693; `save_orig` is true because `SECCOMP_ARCH_NATIVE` is defined).

`bpf_prog_create_from_user` (`net/core/filter.c:1423-1463`):
`bpf_check_basics_ok` (:1047-1056: a NULL program pointer is `-EINVAL`;
the length arms are unreachable after step 1), `bpf_prog_alloc`
(`kernel/bpf/core.c:141-167`, 3.1), `copy_from_user` of the instructions
(`-EFAULT`), `bpf_prog_store_orig_filter` (:1150-1171: a `kmalloc` and a
`kmemdup` of the user's program, kept as `orig_prog` for the cache's
emulation, 2.6), then `bpf_prepare_filter` (:1329-1366):

- `bpf_check_classic` (:1072-1148), 2.5;
- the `trans` hook, `seccomp_check_filter` (`kernel/seccomp.c:280-347`),
  2.5;
- `bpf_jit_compile` (the classic JIT; a weak no-op, `core.c:3069`), so
  `fp->jited` stays 0 and `bpf_migrate_filter` (:1259-1327) runs: a
  `kmemdup_array` of the checked program, a first `bpf_convert_filter`
  pass computing the eBPF length, `bpf_prog_realloc` (`core.c:248-276`, an
  allocation step below the cut, 3.1), the second pass writing the eBPF
  program, `bpf_prog_select_runtime` (`core.c:2527-2580`: no JIT is
  configured, the interpreter for the program's stack depth is selected,
  `bpf_prog_lock_ro`, `bpf_check_tail_call` with no maps), and the free of
  the saved copy.

Back in `seccomp_set_mode_filter`: `NEW_LISTENER` is out of scope; the
`TSYNC` mutex (:2004-2005, `mutex_lock_killable` on `cred_guard_mutex`) is
uncontended on one task and returns 0, its killable arm (:2006, a pending
fatal signal) an explicit stop; under `siglock`, `seccomp_may_assign_mode`
(:437-445: a mode already set must be the same mode; strict after filter
and filter after strict are `-EINVAL`), `has_duplicate_listener` (:1917:
false at its first test, no listener), `seccomp_attach_filter`
(:913-963):

- the path budget (:922-926): the new program's **eBPF** length plus, for
  each filter already on the chain, its eBPF length plus 4, must not exceed
  `MAX_INSNS_PER_PATH` (:240; 32768), else `-ENOMEM`;
- `TSYNC` (:929-937): `seccomp_can_sync_threads` (:490-524) walks the
  thread group, meets only the caller on the one-task group, skips it
  (:503) and returns 0 (:523); the `if (ret)` arm (:933-937, `-ESRCH`
  under `TSYNC_ESRCH`) is declared and never taken here; after the attach,
  `seccomp_sync_threads` (:959-960, :597-645) walks the same group and
  changes nothing; the arms for another thread (:506-520, :615-644) are
  the C's, reached by no run of the single-task representation;
- the `log` (:943) and `wait_killable_recv` (:947) flags;
- `filter->prev = current->seccomp.filter`, `seccomp_cache_prepare`, the
  head pointer, `filter_count++` (:953-956).

Then `seccomp_assign_mode` (:449-465): the mode, `arch_seccomp_spec_mitigate`
unless `SPEC_ALLOW` (a cut: its effect is on speculation-control bits no
operation observes), the syscall work bit. On any failure after `prepare`,
`seccomp_filter_free` (:526) drops the prepared filter.

`prctl(PR_SET_SECCOMP, mode, filter)` (`kernel/sys.c:2551`) reaches
`prctl_set_seccomp` (:2130-2155), which maps mode 1 to
`SECCOMP_SET_MODE_STRICT` with a NULL argument, mode 2 to
`SECCOMP_SET_MODE_FILTER`, anything else to `-EINVAL`, and calls
`do_seccomp` (:2092-2115) with flags 0. `seccomp(2)` (:2117) calls
`do_seccomp` directly: `SET_MODE_STRICT` requires zero flags and a NULL
argument; `GET_ACTION_AVAIL` (:2053-2075) and `GET_NOTIF_SIZES` (:2077)
each require zero flags; the first copies a `u32` and answers `0` for the
eight known actions, `-EOPNOTSUPP` otherwise; the second copies three sizes
out; an unknown op is `-EINVAL`.

### 2.5 The checker: `bpf_check_classic` and `seccomp_check_filter`

`bpf_check_classic` (`filter.c:1072-1148`) walks the program once. Per
instruction: `chk_code_allowed` (:981-1045; a table of 49 classic codes,
anything else `-EINVAL`); then the special cases: `DIV|K` and `MOD|K` with
`k == 0`; `LSH|K` and `RSH|K` with `k >= 32`; `LD|MEM`, `LDX|MEM`, `ST`,
`STX` with `k >= BPF_MEMWORDS` (16); `JA` with `k >= flen - pc - 1`; the
eight conditional jumps with `pc + jt + 1 >= flen` or `pc + jf + 1 >=
flen`; `LD|{W,H,B}|ABS` with `k >= SKF_AD_OFF` (0xfffff000) that is not a
known ancillary load. The last instruction must be `RET|K` or `RET|A`, and
then `check_load_and_stores` (:928-979) runs: a forward dataflow over the
16 memory cells (`masks` is a `kmalloc_array` of `flen` halfwords, 3.1)
whose validity set at an instruction is the intersection over its incoming
edges (`masks[target] &= memvalid`), so it rejects a load of a cell that
some path has not stored.

`seccomp_check_filter` (`seccomp.c:280-347`) walks the checked program and
rewrites in place: `LD|W|ABS` becomes `LDX|W|ABS` and must have `k < 64`
and `k & 3 == 0`; `LD|W|LEN` and `LDX|W|LEN` become immediate loads of 64
(`sizeof(struct seccomp_data)`); 38 further codes pass unchanged;
everything else (the half-word and byte loads, `IND`, `MSH`, `MOD`, the
ancillary loads that passed the classic checker) is `-EINVAL`. Note the
order: the original program was already saved by
`bpf_prog_store_orig_filter`, so `orig_prog` holds the un-rewritten codes
and the cache's emulation (2.6) matches on `LD|W|ABS`, not on the rewritten
`LDX`.

### 2.6 The cache: `seccomp_cache_prepare` and `seccomp_is_const_allow`

`seccomp_cache_prepare` (:881-898) builds the new filter's `allow_native`
bitmap from the previous filter's (`bitmap_copy`) or from all-ones
(`bitmap_fill`) and, for every number `0..462` whose bit is still set,
clears it unless `seccomp_is_const_allow(orig_prog, {nr, arch})` holds
(:839-873). A bit can only be cleared, never set, so the chain's cache is
monotone by construction (4.6).

`seccomp_is_const_allow` (:762-836) first returns true for
`seccomp_uprobe_exception` (:736-754: `nr == __NR_uretprobe`, 335), then
emulates the program with one abstract register: `LD|W|ABS` of `nr` or
`arch` loads the constant, any other offset returns false; `RET|K` answers
`k == SECCOMP_RET_ALLOW`; `JA` and the four `|K` conditional jumps follow
the constant; `AND|K` masks; any other instruction returns false; running
off the end is a `WARN_ON` and false. **The uretprobe exception**: bit 335
is set in every filter's bitmap whatever its program says, so the cache
answers `ALLOW` for call 335 before any program runs, and a filter cannot
restrict it on this architecture. The mirror reproduces this, and both
statements 1 and 2 of 4.6 carry it as their one stated exception. On this
oracle an allowed call 335 answers `-ENOSYS` (`UPROBES` absent, above).

### 2.7 Running: the engine seam

`bpf_prog_run_pin_on_cpu` (`include/linux/filter.h:722-730`) disables
migration and calls `bpf_prog_run` → `__bpf_prog_run` (:681) →
`prog->bpf_func(ctx, insnsi)`, the interpreter `___bpf_prog_run`
(`kernel/bpf/core.c:1811`) selected for the program's stack size. The
stats branch is off. Everything from :426 down is the service of 4.4:
`kernel/bpf/core.c` is never listed in `correspondence/kcov.json`, and
`include/linux/filter.h` is not either, so the inlined wrapper's points
are not witnesses.

### 2.8 Inheritance and release

`copy_process` (`kernel/fork.c:2583`) calls `copy_seccomp` (:1926-1957):
`get_seccomp_filter(current)` (`seccomp.c:971-980`: one `refs` and one
`users` increment on the head filter, nothing if there is none), the
`seccomp` struct is copied, no-new-privs is propagated, the work bit set
if a mode is set. This runs in the parent's `clone`, inside the parent's
window, and is witnessed there. The child's KCOV is cleared
(`kcov_task_init`, `fork.c:1185`), so a child's calls are not on the
parent's coverage; the child's pending set starts empty and its action
table is a copy of the parent's, handler included.

At exit, `do_exit` calls `kcov_task_exit` at `kernel/exit.c:894`, then
`exit_signals` (:902) and `seccomp_filter_release` (:904), then `exit_files`
(:949). So the release runs after the exiting task's coverage has stopped:
**no window ever contains it**, in the child or in the trace process. What
it does (`seccomp.c:572-585`: clear the head under `siglock`, then
`__seccomp_filter_orphan` (:534) walking `prev` while `users` reaches zero,
and `__put_seccomp_filter` (:543) walking while `refs` reaches zero,
freeing with `seccomp_filter_free` :526) is applied by the mirror as an
environment effect of the child's exit, with no decisions (4.5, 5): for a
sandboxed child of a filtered trace process, one `users` and one `refs`
decrement on the head, and nothing freed, since the parent still holds it.
For a task without a filter the function takes the lock, clears nothing and
walks nothing.

### 2.9 Strict mode

`seccomp_set_mode_strict` (:1419-1439): `seccomp_may_assign_mode`, then
`seccomp_assign_mode(current, STRICT, 0)` (`disable_TSC` is a cut). From
then on `__secure_computing_strict` (:1059-1077) allows `read`, `write`,
`exit`, `rt_sigreturn` and `uretprobe` (`mode1_syscalls`, :1048-1057) and
otherwise sets `mode = SECCOMP_MODE_DEAD` (:1074), logs `KILL_THREAD` with
`SIGKILL`, and `do_exit(SIGKILL)`. `exit_group` is not on the list: a strict
task must leave with `exit`.

### 2.10 The companions (`kernel/sys.c`)

`PR_GET_SECCOMP` (:2548) returns the mode (`prctl_get_seccomp`,
`seccomp.c:1407`, no branch). `PR_SET_NO_NEW_PRIVS` (:2632-2636): `arg2 ==
1` and `arg3..5 == 0` or `-EINVAL`; `task_set_no_new_privs`, a `sched.h`
inline. `PR_GET_NO_NEW_PRIVS` (:2638-2641): all arguments zero or
`-EINVAL`; the bit. `capset` for the capability drop is in
`kernel/capability.c` and `security/commoncap.c`. None of these files is
anchored (6.3): the effect on the task (the bit, `cap_effective`) is
mirrored as data, and the next install or query observes it.

## 3. Hidden inputs

### 3.1 Allocation sites (kind 305, the existing hook)

The hook records slab allocations (`slab_alloc_node`) and page allocations
(`__alloc_pages_noprof`) whose entry's own return address lies in an armed
range (`kernel/patches/gen-choice-stream.py:1060-1078`), with up to four
return addresses above it; the bulk allocators and the percpu allocator
are unhooked by construction. One install, in order:

| # | Site | Allocator | Recorded? |
| --- | --- | --- | --- |
| 1 | `seccomp_prepare_filter` `kzalloc(sfilter)` (`seccomp.c:688`) | slab | yes |
| 2 | `bpf_prog_alloc_no_stats` `__vmalloc(size)` (`core.c:105`) | pages, from `mm/vmalloc.c` | no |
| 3 | `bpf_prog_alloc_no_stats` `kzalloc(aux)` (`core.c:109`) | slab | yes |
| 4 | `bpf_prog_alloc_no_stats` `alloc_percpu_gfp(active)` (`core.c:114`) | percpu | no |
| 5 | `bpf_prog_alloc` `alloc_percpu_gfp(stats)` (`core.c:151`) | percpu | no |
| 6 | `bpf_prog_store_orig_filter` `kmalloc(fkprog)` (`filter.c:1156`) | slab | yes |
| 7 | `bpf_prog_store_orig_filter` `kmemdup(filter)` (`filter.c:1163`) | slab | yes |
| 8 | `check_load_and_stores` `kmalloc_array(masks)` (`filter.c:935`) | slab | yes |
| 9 | `bpf_migrate_filter` `kmemdup_array(old_prog)` (`filter.c:1277`) | slab | yes |
| 10 | `bpf_prog_realloc` `__vmalloc` (`core.c:260`), when the eBPF image needs more pages (:257) | pages, from `mm/vmalloc.c` | no |
| 11 | `bpf_convert_filter` second pass `kcalloc(addrs)` (`filter.c:594`) | slab | yes |

Sites 2 and 10 reach the page allocator from inside `mm/vmalloc.c` (as do
the `vm_struct`, `vmap_area` and page-array slab allocations `__vmalloc`
makes on the way), so the hook's range test never sees a seccomp frame;
sites 4 and 5 are percpu. All four are **unrecorded and assumed to
succeed**, declared as such in `AllocSite`'s class from the start, with
their `-ENOMEM` arms modelled but unexercised (9.3). A real `-ENOMEM` there
surfaces as a result mismatch, the fail-noisy outcome. `bpf_prog_realloc`
is below the cut (6.3) and its page test is not a mirror decision: the
mirror neither evaluates it nor needs `struct bpf_prog`'s layout.

Two more sites belong to the actions and the child:

| # | Site | Allocator | Recorded? |
| --- | --- | --- | --- |
| 12 | `__sigqueue_alloc` (`signal.c:404-442`), one per `TRAP` or kill, already `AllocSite.sigqueueAlloc` | slab | yes: the seccomp traces' armed ranges include it |
| 13 | the parent's `clone`: a task, an mm, `dup_fd`'s `files_struct` (`fs/file.c:314`) and more | slab and pages, none armed | no: the clone is assumed to succeed |

### 3.2 Nothing else

seccomp on these paths reads no clock, draws no random bytes, arms no
timer, queues no work, takes no scheduling choice (`migrate_disable` is
not a scheduling point) and touches no per-cpu state the mirror would
have to know. The remaining inputs are fixture constants, checked once per
trace rather than recorded:

- `kernel.seccomp.actions_logged` (`/proc/sys/kernel/seccomp/actions_logged`),
  read by the guest into its `LEANUX_FIXTURE` row and compared with the
  mirror's default (`harness/linux.py`, beside `max_user_watches`);
- the task's capability set (root, all capabilities) and no-new-privs bit
  (clear) at trace start: the mirror's initial task state.

`instruction_pointer` (`populate_seccomp_data`, :265, `KSTK_EIP(task)`) is
recorded at that line as kind 312 (`HiddenSite.seccompIp`, 8 bytes, class
`address`; the hook shares the line, the anchored file keeps its length),
once per `__seccomp_filter` entry that builds its own `seccomp_data` (:1258,
before the cache check), in the task's or the child's stream. The mirror
consumes it at its populate point and the engine serves offsets 8..15 from
it, so a filter that branches on the pointer runs the same program on the
same value (the `s_ip_*` traces, 7). Until the pre-release review it was the
one hidden value deliberately not recorded and such filters stopped at the
seam.

### 3.3 The translated program: a record, not a hidden input (kind 309)

The eBPF program the translation writes is observable only through the
engine's results and the path budget. A record-only hook makes it data:
at the end of `bpf_migrate_filter`'s second pass, before
`bpf_prog_select_runtime` locks the pages, one kind-309 record per emitted
`bpf_insn` (one payload word, the instruction's eight bytes; the record
header carries kind, length and sequence), then one record with the eBPF
length. A choice record carries at most five payload words
(`KCOV_CHOICE_MAX_WORDS`, `gen-choice-stream.py:64`), which rules out one
record for the whole program; per-instruction records keep the diagnostic
local (the first differing instruction, by index) and the mirror consumes
them in order like every other kind, which is why they are preferred to a
length-plus-hash record. About 80 records per generated install; the
4096-instruction budget traces produce some 8,000, well inside the area.
This is a record-only kernel change under the approved class: it lands
with the per-merge signoff and the new identity, with its one-off mutant
(8); it is not a separate ruling.

## 4. The mirror

### 4.1 State (`Leanux/Kernel/Defs.lean`, `Leanux/Seccomp/Defs.lean`)

`Task` gains:

```
seccomp      : SeccompState      -- current->seccomp
noNewPrivs   : Bool := false     -- task_no_new_privs
capSysAdmin  : Bool := true      -- cap_effective ∋ CAP_SYS_ADMIN
sigsys       : Disposition := .handler   -- sighand->action[SIGSYS-1]: handler | dfl | dflImmutable
sigpending   : Bool := false     -- TIF_SIGPENDING
```

```
inductive SeccompMode | disabled | strict | filter | dead
structure SeccompFilter where
  id        : FilterId            -- allocation identity, from the kind-305 record
  refs      : Nat                 -- refcount_t refs
  users     : Nat                 -- refcount_t users
  log       : Bool
  waitKillableRecv : Bool
  allowNative : BitVec 463        -- action_cache.allow_native
  prev      : Option FilterId
  prog      : BpfProg             -- the translated program (4.3)
  origProg  : ClassicProg         -- orig_prog, the user's program as copied
structure SeccompState where
  mode        : SeccompMode := .disabled
  filterCount : Nat := 0
  filter      : Option FilterId := none
```

`Kernel` gains `seccompFilters : TreeMap FilterId SeccompFilter`, the tree
(here a list through `prev`) shared by every task that holds it, and
**`child : Option Task`**, the sandboxed child of 6.2. `Kernel.task` stays
the trace process. The runner selects `current` (the trace process, or the
child while a child probe's steps run), and every function in
`Seccomp/*` and `Signal.lean` reads and writes `current` rather than
`Kernel.task` (today `Signal.lean:13` fixes the target as the one task;
the interface commit makes it a parameter, M2). The child is created at
the probe from the parent's state by `copy_seccomp`'s effects (2.8: the
`seccomp` struct copied, the head's counts incremented, `noNewPrivs`
propagated, `capSysAdmin` and the action table copied, the pending set
empty) and destroyed at the parent's `wait4` after the exit effect of 2.8
is applied. The child holds no file table of its own: no modelled path in
the child touches a file, and the runner stops with `invariant` if one
did. The notifier, lock and wait-queue fields of `seccomp_filter` are not
mirrored (9.2).

### 4.2 Classic programs and the checker (`Leanux/Seccomp/Classic.lean`)

```
structure SockFilter where code : UInt16; jt : UInt8; jf : UInt8; k : UInt32
abbrev ClassicProg := Array SockFilter

def chkCodeAllowed : UInt16 → Bool                                  -- filter.c:981
def bpfCheckClassic : ClassicProg → M (Except Errno Unit)            -- :1072
def checkLoadAndStores : ClassicProg → M (Except Errno Unit)         -- :928
def seccompCheckFilter : ClassicProg → M (Except Errno ClassicProg)  -- seccomp.c:280
```

Each walks the program in the C's order and reports the C's decisions (the
`switch` on the code, each special-case comparison, the final `RET` test,
the dataflow's per-cell test). `seccompCheckFilter` returns the rewritten
program. `bpfCheckClassic`'s `kmalloc_array` of `masks` is an allocation
step with its `-ENOMEM` arm. Every per-instruction decision here is
**repeatable** (`Decision.repeatable`, `Leanux/Kernel/Decision.lean:1868`):
one install evaluates it once per instruction, the check compares the set
of (decision, outcome) pairs, and the mirror emits each pair once per
operation.

### 4.3 Translation (`Leanux/Seccomp/Translate.lean`)

```
structure BpfInsn where code : UInt8; dst : UInt8; src : UInt8; off : Int16; imm : Int32
structure BpfProg where insns : Array BpfInsn; stackDepth : Nat; len : Nat

def bpfConvertFilter (prog : ClassicProg) (emit : Bool) (addrs : Option (Array Nat))
    : M (Except Errno (Array BpfInsn × Nat × Bool))                 -- filter.c:576
def bpfMigrateFilter : BpfProg → M (Except Errno BpfProg)            -- :1259
def bpfPrepareFilter : BpfProg → M (Except Errno BpfProg)            -- :1329
def bpfProgCreateFromUser : SockFprog → M (Except Errno BpfProg)     -- :1423
```

`bpfConvertFilter` is the C's two-pass conversion: the three-instruction
prologue (`A ^= A`, `X ^= X`, `CTX = ARG1`; the `seen_ld_abs` extension is
dead for seccomp programs because every `LD|ABS` was rewritten to
`LDX|ABS`, so the `convert_bpf_extensions`/`convert_bpf_ld_abs` arms are
`invariant` stops), the per-instruction arms as the C has them (ALU as-is
with the `DIV|X`/`MOD|X` zero guard, the jump forms with `BPF_EMIT_JMP`'s
range check and its negative-immediate temporary, `RET|K` as two
instructions, stack stores and loads at `-(4k + 4)` with the stack-depth
update, immediates, `TAX`/`TXA`, the `LEN` arm (dead after the rewrite),
`LDX|ABS|W` as a context load), the `addrs` table, the pass-count
convergence test (`pass > 2` is `-EINVAL`). The per-instruction decisions
of both passes are repeatable, as in 4.2. The eBPF length is what the
path budget (2.4) consumes, so the mirror must get it exactly; the
kind-309 records (3.3) compare the program instruction by instruction, and
the Lean-side check of 8 compares its behaviour.

### 4.4 The engine contract (`Leanux/Seccomp/Engine.lean`)

The seam is `kernel/seccomp.c:426`. Above it the mirror is anchored
control flow; below it is a service with this contract:

```
/-- The 64-byte seccomp_data image the program reads through CTX. -/
structure SeccompData where
  nr   : Int32
  arch : UInt32
  ip   : Option UInt64      -- none: not a hidden input (3.2)
  args : Vector UInt64 6

inductive EngineStop
  | unsupportedRead (offset : Nat)       -- a CTX read of the ip words
  | unsupportedInsn (pc : Nat) (code : UInt8)
  | fault (what : String)                -- out-of-range jump, bad CTX offset

/-- A model of the kernel's eBPF interpreter restricted to one entry:
    run `prog` on `ctx` with R1 = CTX, a zeroed 512-byte stack, and return R0's
    low 32 bits as the C's `unsigned int (*bpf_func)(ctx, insnsi)` does. -/
class BpfEngine (E : Type) where
  run : E → BpfProg → SeccompData → Except EngineStop UInt32
```

Terms an instance must satisfy, stated once in the file so an external
ISA model can be checked against them. They are **premises**, not
consequences of the class: `BpfEngine` supplies a `run` field and nothing
proves an arbitrary instance meets them; a theorem parametric in `E` takes
them as hypotheses, and `MiniInterp` is the one instance whose adherence
the tests and the kind-309 byte comparison exercise (pre-release review
finding 11):

1. `CTX` reads are `LDX_MEM W` at 4-aligned offsets below 64: offset 0 is
   `nr` as a 32-bit value, 4 is `arch`, 8 and 12 are the two halves of
   `ip` (a stop when `ip = none`), `16 + 8k` and `20 + 8k` the halves of
   `args[k]`, little-endian.
2. The stack is 16 words at `FP - 4 .. FP - 64`, zero before the run;
   `STX_MEM W` and `LDX_MEM W` from `FP` only.
3. ALU32 semantics are the interpreter's (`core.c:1811`; the `ALU` and
   `SHT` macros and the masking comment at :1841-1866): 32-bit wrap;
   shifts by a register mask the count to 5 bits (the interpreter's
   convention; the kernel's comment there says a JIT must not add the
   mask, so an ISA model of a JIT states its own); `NEG` is 32-bit negate;
   `DIV`/`MOD` by a zero register never reach the engine (the translation's
   guard returns 0 before them, 4.3), by a zero immediate never pass the
   checker.
4. **Register width.** Every write to `A`, `X` and `TMP` the translation
   emits is 32-bit and zero-extending (ALU32, `MOV32_IMM`, `LDX_MEM W`), so
   the 64-bit `BPF_JMP`-class comparisons it emits compare zero-extended
   values. `MiniInterp` holds registers as `UInt32` under that invariant;
   an instance over `UInt64` must zero-extend on those writes to meet the
   same terms. Jumps are `off`-relative, 16-bit signed, resolved by the
   translation; `EXIT` returns `R0`; `MOV64_REG` copies.
5. The result is the low 32 bits of `R0`; the engine has no other effect.

The mirror's instance, `MiniInterp`, implements exactly the opcodes the
translation of a seccomp-checked program can emit (about twenty) and
answers `unsupportedInsn` for anything else, so a translation defect
cannot be absorbed by a permissive engine. The user's eBPF JIT project
would provide a second instance over the same `BpfProg`; the mirror's
`seccompRunFilters` is parametric in the instance, and the differential
check runs with `MiniInterp`. No decision inside `run` is a mirror
decision: the C's interpreter is not in `kcov.json`'s `files`, and the
mirror emits none for it. The same holds for `kernel/bpf/core.c` as a
whole (3.1).

### 4.5 seccomp proper (`Leanux/Seccomp/Filter.lean`, `Syscalls.lean`, `Signal.lean`)

Functions, each with the C's decisions in the C's order:

```
def seccompIsConstAllow : ClassicProg → Int32 → UInt32 → M Bool       -- :762
def seccompCachePrepare : FilterId → M Unit                           -- :881
def seccompPrepareFilter : SockFprog → M (Except Errno FilterId)      -- :661
def seccompAttachFilter : Flags → FilterId → M (Except Errno Unit)    -- :913
def seccompMayAssignMode : SeccompMode → M Bool                       -- :437
def seccompAssignMode : SeccompMode → Flags → M Unit                  -- :449
def seccompSetModeFilter : Flags → Option SockFprog → M Int           -- :1947
def seccompSetModeStrict : M Int                                      -- :1419
def doSeccomp : Nat → Flags → Arg → M Int                             -- :2092
def prctlSetSeccomp / prctlGetSeccomp / prctlNoNewPrivs               -- sys.c
def seccompRunFilters [BpfEngine E] : SeccompData → M (UInt32 × Option FilterId) -- :406
def seccompLog : Int32 → Int → UInt32 → Bool → M Unit                 -- :1000
def seccompFilter [BpfEngine E] : Int32 → SeccompData → M FilterOutcome -- :1244
def secureComputing [BpfEngine E] : Syscall → M FilterOutcome          -- :1378
def getSeccompFilter : M Unit                                          -- :971 (the parent's clone)
-- Signal.lean, the extension
def forceSigInfoToTask : SigInfo → SigHandler → M Int                  -- signal.c:1328
def completeSignalWake : Nat → M Unit                                  -- :994, the wake arm
def signalWakeUpState : M Unit                                         -- :759
```

`FilterOutcome` is `proceed | skip (ret : Int) | trapped (nr data) |
killed (signal)`. `secureComputing` runs **before every operation's
system call** once the task's mode is set, with the call's number and,
for probe calls, its arguments; for the harness's own calls (every op
that is not a probe) the data is `{nr, arch, args := 0}`: the chain is
const-allow for those numbers by the rule of 6.2, so the cache answers
and the arguments are never read. If the cache does not answer for a
non-probe number, the mirror stops with `invariant` ("harness call not
const-allowed"): the trace is outside the domain by construction and the
guest would have been running an unverified filter on itself.

`seccompCachePrepare` is the C's loop over 463 numbers, each an emulation
run with the decisions of 2.6; every decision in it is repeatable, the
pairs are emitted once per operation, and the 463 runs stay in Lean where
they are cheap.

The signal extension replaces the `unsupported` stops of `Signal.lean`
that an unblocked `SIGSYS` reaches with the arms of 2.2: in
`sigTaskIgnored` the handler and forced-default dispositions; in
`__send_signal_locked` the real siginfo (its three fields are kept as the
predicted handler record, the queue entry itself is still not a list, the
P design's shape deviation); in `wantsSignal` the unblocked arms; in
`completeSignal` the wake arm with the `sig_fatal` chain; new
`forceSigInfoToTask` and `signalWakeUpState`. Stop and continue signals,
group delivery, real-time signals and a second thread stay `unsupported`.
Delivery (2.2) is an environment effect of the `trapped` outcome, and the
child's exit (2.8) an environment effect of the `killed` and exited
outcomes; neither emits decisions.

### 4.6 Proof-shaped statements

No theorem is written (AGENTS.md). The functions are shaped so these can be
stated over them without restructuring; the Codex spike's charter pattern
applies if the user opens one. Statements 1 and 2 share one exception, the
uretprobe bit of 2.6, stated once.

1. **Chain monotonicity.** For a task state `t` and an accepted filter `f`,
   `ACTION_ONLY (runFilters (attach f t) d) ≤ ACTION_ONLY (runFilters t d)`
   for every `d`, where `runFilters` includes the cache. This needs 2 and
   3: the new bitmap is a subset of the old (`bitmap_copy` then clears
   only), and a cache hit on the old chain means every old program answers
   `ALLOW` on `d`, so the new minimum over a superset of programs is at
   most `ALLOW`. At `nr = 335` both sides are `ALLOW` by the exception.
2. **Cache soundness.** `seccompIsConstAllow p d.nr d.arch = true` implies
   `engine.run (translate p) d = ALLOW` for every `args` and `ip`, for any
   engine satisfying 4.4, except at `nr = 335`, where the cache answers
   without the program.
3. **Checker soundness.** A program accepted by `bpfCheckClassic ∘
   seccompCheckFilter` terminates within `len` steps (all jumps forward),
   ends at a `RET`, loads only stored cells, reads CTX only in bounds and
   aligned, never divides by a zero immediate.
4. **Translation correctness.** For an accepted program `p` and data `d`,
   `classicRun p d = engine.run (translate p) d`, where `classicRun` is a
   direct semantics of the seccomp-checked classic language (a reference
   function the mirror ships for the executable check of 8, not used on
   the modelled path). `classicRun` must define `LSH|X` and `RSH|X` with a
   count of 32 or more as the eBPF interpreter does (masked to 5 bits) and
   `DIV|X`/`MOD|X` by zero as "the program returns 0": under the naive
   classic reading the statement is false, and the mirror's reference is
   the kernel's semantics, not the textbook's.

4 is the one the engine seam makes precise: the left side is the mirror's,
the right side is the ISA model's, and the contract of 4.4 is the
interface between the two projects.

## 5. Environment rules (`Leanux/Env.lean`)

- The trace process starts as root with all capabilities, no-new-privs
  clear, mode disabled, no filter, `SIGSYS` with a handler (installed by the
  guest at setup, so a `TRAP` never kills the trace process), `SIGPIPE`
  blocked as the pipes fixture has it.
- Reserved descriptors: the fixture's 0-7, plus 8 in a trace that declares
  `seccomp_child` (the second KCOV descriptor, 6.2), reported in the
  `LEANUX_FIXTURE` row as today's `reserved` list (`harness/linux.py:600`
  already varies it by fixture). `seccomp_child` and a network fixture are
  mutually exclusive: 8 and 9 are W8's `INJECT_FD` and `PIN_FD`
  (`harness/guest.c:79-80`) and 7 is the netlink socket; the validator
  rejects the combination and the interface document's table records the
  exclusivity (the coordinator's, 12).
- `actions_logged` is the kernel default, checked by the fixture row.
- The prefill fixture [USER 2026-10-12: queued]: a trace declaring
  `"seccomp_prefill": N` (1-8; never with a network fixture or a steering
  schedule) starts with no-new-privs set and `N` copies of a fixed
  3990-instruction program on its chain, installed by the guest before the
  window (`harness/guest.c` `SECCOMP_PREFILL_*`): `nr` loaded, a `JA` chain
  only for a dummy number outside the probe set and the cached range, `ALLOW`
  otherwise, so every probe is a cache hit through the chain. The mirror's
  initial task state carries the chain, reconstructed by its own translation
  of the same program under the record-free local instance and the
  decision-free cache emulation (`Leanux/Seccomp/Prefill.lean`,
  `Env.seccompPrefill`): a fixture assumption like the descriptors, outside
  every window; the kernel's `total_insns` at the first recorded install is
  the evidence that the reconstruction's lengths are the kernel's. Each copy
  is 3995 eBPF instructions, 3999 with the walk's penalty: eight leave 776 of
  `MAX_INSNS_PER_PATH` for the recorded installs (7).
- The child's exit effect (2.8): one `users` and one `refs` decrement on the
  head filter the parent holds; the child's task object is dropped at the
  parent's `wait4`. The `TRAP` delivery effect (2.2): `SIGSYS` removed
  from the pending set, `sigpending` cleared, `blocked` unchanged after the
  handler returns. Both are runner effects with no decisions.

## 6. Harness and guest

### 6.1 Operations

Five operations (`harness/trace.py` `FIELDS`, `OPCODES`;
`contracts/trace-v1.md`; `harness/guest.c`), the opcodes allocated in the
interface commit:

| Operation | Fields | Wire (`struct operation`) | Opcode |
| --- | --- | --- | --- |
| `seccomp_install` | `via` (seccomp, prctl), `flags` (names: log, spec_allow, tsync, new_listener, tsync_esrch, wait_killable_recv, or a raw bit for the mask arm), `filter` (list of `[code, jt, jf, k]`, or `null` for the NULL-pointer arm), `len` (optional override, for the length arms), `bad` (optional: `fprog` or `insns`, an unmapped pointer for the two `-EFAULT` arms) | `a = via`, `b = flags ∣ bad << 16`, `payload = filter`, `value = len` | 30 |
| `seccomp_probe` | `nr`, `args` (six `u64`, default 0), `where` (self, child), `strict` (child only: `null`, seccomp, prctl) | `a = nr`, `b = where ∣ strict << 8`, `payload = args` | 31 |
| `seccomp_prctl` | `cmd` (set_no_new_privs, get_no_new_privs, get_seccomp), `arg2..arg5` (default 0, for the `-EINVAL` arms) | `a = cmd`, `payload = args` | 32 |
| `seccomp_capdrop` | none: `capset` without `CAP_SYS_ADMIN` in the effective, permitted and inheritable sets | | 33 |
| `seccomp_query` | `cmd` (get_action_avail, get_notif_sizes), `action`, `flags` | `a = cmd`, `b = action`, `value = flags` | 34 |

The observation for every op is `struct observation`'s `ret` and `error`
as today. `seccomp_probe` adds: for a `TRAP`, the handler's record
`sigsys: {nr, data, arch}` (the handler stores `si_syscall`, `si_errno`,
`si_arch` into a static the op reads afterwards); for a child probe, a
`child` record: `strict_ret` (the child's own strict call, when asked:
`-EINVAL` after an inherited filter), then one of `ret` (from the shared
page, the child left normally with `exit_group` or `exit`), `exited:
status` (the child left without writing, which the mirror never predicts)
or `signal` (31 `SIGSYS`, 9 `SIGKILL`) from `waitpid`. The `ret` after a
`TRAP` is the call number (2.2), predicted by the mirror; step 0 confirms
it is stable, else it becomes a declared exclusion.

The validator rejects: `where = self` once any installed filter of the
trace **may kill**, which is a syntactic scan for a `RET|K` whose action is
`KILL_THREAD`, `KILL_PROCESS` or non-canonical, a `RET|A` (the accumulator
may hold anything, including 0, which is `KILL_THREAD`), or a `DIV|X` or
`MOD|X` (a zero `X` returns 0 through the translation's guard); `strict`
outside a child probe; `seccomp_child` with a network fixture; `tsync`,
`new_listener`, `wait_killable_recv` flags outside the control suite; a
probe `nr` outside the probe set of 6.2; a filter longer than 4096 outside
the hand-written suite. The scan is conservative by design: it is enforced
without predicting the chain, and the three extra forms are exercised in a
child (7) so their arms are witnessed, not merely avoided.

### 6.2 The self-sandboxing rule

A filter installed by op 30 governs the trace process, including the
calls the harness makes after it: the fd ops of a mixed trace, `clone`
and `wait4` for a child probe (glibc's `fork` is a `clone` between two
`rt_sigprocmask`), `rt_sigreturn` after a trap, the KCOV status ioctls and
the `write` of the result at the end. Three rules make this safe and, more
importantly, make the harness's calls invisible to the engine:

1. **Probe numbers.** A filter in the corpus may restrict only the probe
   set: `getuid` 102, `getgid` 104, `geteuid` 107, `getegid` 108 (in
   range, no arguments, no side effects, result 0 as root, so a filter's
   `args` tests are on values the op controls), `1000` (out of range:
   never cached, `-ENOSYS` when allowed), and `uretprobe` 335 for its
   control (`-ENOSYS` when allowed, 2.6). Every other number must be
   allowed, and allowed **constantly**: the filter's prologue loads `arch`
   and `nr` and returns `ALLOW` for any number outside the probe set
   using only the instructions `seccomp_is_const_allow` follows (2.6).
   Then every harness call is a cache hit: no program runs, the arguments
   (buffer addresses and the like, which the mirror does not know) are
   never read, and the coverage inside an op's window is the fixed
   `__secure_computing → __seccomp_filter → seccomp_run_filters →
   seccomp_cache_check_allow` path, which the mirror emits for every op
   after a mode is set (4.5). The generator builds filters from this
   prologue; the hand-written set respects it; the mirror's `invariant`
   stop (4.5) catches any filter the kernel accepted but the rule did not
   hold for. The libc calls none of 102, 104, 107, 108 on its own.
2. **Kills happen in a child.** A probe whose chain may kill runs in a
   sandboxed child: the trace process `fork`s (the child inherits the
   chain, 2.8, with the fork's `get_seccomp_filter` in the parent's
   window), the child enables its own KCOV on descriptor 8 (opened,
   initialised and mapped `MAP_SHARED` by the trace process at setup,
   before descriptors are counted and before the rlimit is lowered, so
   the mapping is visible to both), zeroes the area's count, optionally
   sets strict mode (reporting its result), issues the probe, writes `ret`
   into a shared anonymous page, and leaves with `exit_group` (or `exit`
   under strict). The trace process `waitpid`s and reads the child's area
   from the shared mapping. The child's window is [probe, its own
   `kcov_task_exit`], which ends at `kernel/exit.c:894`: it holds the
   action arm, the signal generation, `get_signal`'s fatal arm and
   `do_coredump` for a kill, and the start of `do_exit`; it never holds
   `seccomp_filter_release` (:904) or `exit_files` (:949), which is why
   the release is an environment effect (2.8, 5) and the child's
   file-table teardown is never witnessed. `RLIMIT_CORE` is zero in the
   trace process so a `SIGSYS` death attempts no core file (2.2). A new
   child can re-enable the same descriptor because `kcov_task_exit` resets
   it (`kernel/kcov.c:397-398`). The parent's `clone` also runs
   `copy_files → dup_fd` (`fs/file.c:314`, a listed file, an unlisted
   function) with `copy_fd_bitmaps` (:56) and `sane_fdtable_size` (:295)
   inside the parent's window: tolerated unless a span line of a listed
   decision is hit; step 0 confirms on one child probe.
3. **Traps are caught.** The guest installs a `SIGSYS` handler at setup
   (`SA_SIGINFO`, no `SA_NODEFER`) that records the three fields; with it,
   `TRAP` returns to the op in both modes. The handler's cost on the mirror
   side is the signal extension of 4.5, about 0.1 WU, not the ten lines the
   first draft claimed.

Strict mode is child-only (rule 2) because a strict trace process could
not read its coverage back (the ioctls are not on the list, 2.9).

The alternative to descriptor 8 is a `CLONE_VM` child whose own KCOV
mapping lands in the shared address space; it avoids the reserved
descriptor at the cost of a separate stack and a clone flag the fixture
has not used. Noted, not chosen (13).

### 6.3 Coverage

A probe with no mode set covers nothing anchored: the syscall entry's fast
path never reaches `__secure_computing` (2.1), so the check's "no coverage
in anchored files" rule fails the operation. The validator therefore
requires every probe to follow an install, or to be a strict child (which
sets its own mode), and the corpus never probes after only rejected
installs (`scripts/seccomp-corpus.py` checks its own traces; the generator
installs first). Chosen over declaring such probes data-only because
data-only is by operation name (`data_only_operations`) while this is a
property of the trace's state, and a rule the validator and the corpus
carry keeps the check fail-closed on the case it cannot tell apart (an
install the kernel rejected) [AGENT, X].

`correspondence/kcov.json` gains the files `kernel/seccomp.c`,
`net/core/filter.c`; the functions of section 2 (`__secure_computing`,
`__seccomp_filter`, `seccomp_run_filters`, `seccomp_cache_check_allow`,
`seccomp_cache_check_allow_bitmap`, `populate_seccomp_data`,
`seccomp_log`, `__secure_computing_strict`, `seccomp_set_mode_filter`,
`seccomp_set_mode_strict`, `seccomp_prepare_user_filter`,
`seccomp_prepare_filter`, `seccomp_check_filter`, `seccomp_attach_filter`,
`seccomp_may_assign_mode`, `seccomp_assign_mode`, `seccomp_cache_prepare`,
`seccomp_cache_prepare_bitmap`, `seccomp_is_const_allow`,
`seccomp_uprobe_exception`, `has_duplicate_listener`, `seccomp_filter_free`
(reached from a failed attach in the trace process's window),
`get_seccomp_filter`, `__get_seccomp_filter`, `do_seccomp`,
`prctl_set_seccomp`, `prctl_get_seccomp`, `seccomp_get_action_avail`,
`seccomp_get_notif_sizes`, `bpf_prog_create_from_user`,
`bpf_prepare_filter`, `bpf_migrate_filter`, `bpf_check_basics_ok`,
`bpf_check_classic`, `chk_code_allowed`, `check_load_and_stores`,
`bpf_convert_filter`, `bpf_prog_store_orig_filter`,
`bpf_release_orig_filter`, `__bpf_prog_release`, `bpf_prog_destroy`); in
the already-listed `kernel/signal.c`, `force_sig_seccomp`,
`force_sig_info_to_task` and `signal_wake_up_state` beside the eight the
pipes listed; and the `cut_functions` the epoll design introduces, here
`bpf_prog_realloc` and `bpf_prog_select_runtime`. `kernel/bpf/core.c` is
not listed. The release walkers (`seccomp_filter_release`,
`__seccomp_filter_release`, `__seccomp_filter_orphan`,
`__put_seccomp_filter`) are not listed: no window contains them (2.8).

`kernel/sys.c` and `kernel/capability.c` are not listed, and before a mode
is set ops 32 and 33 touch no anchored file at all; after one is set they
touch only the cache path. Listing `kernel/sys.c` would anchor `prctl`'s
sixty-arm switch for two arms of ours, and `prctl_get_seccomp` has no
branch to witness anyway. So ops 32 and 33 are declared **data-only** in
the check (`evaluator/check.py`, beside the `wg_flood` and `wg_batch`
special cases at :846-858): exempt from "no coverage in anchored files"
(:872) and "no model decision" (:892), with any decisions they do report
(the cache path once a mode is set) checked as usual. Their evidence is
the data: the next install's `-EACCES` or 0, `get_no_new_privs`'s answer,
`get_seccomp`'s mode. The declaration is recorded in `kcov.json` as a
named list of unwitnessed operations.

The existing suites are unaffected by listing `kernel/seccomp.c` and the
three signal functions: no process in them sets a mode; `copy_seccomp` and
`seccomp_filter_release` run at every fork and exit but outside every
window in those suites (the pin holder forks at batch level; exits follow
the result line and, in any case, follow `kcov_task_exit`); nothing in them
raises `SIGSYS`.

## 7. Generator and corpus

`scripts/seccomp-corpus.py` writes `corpus/seccomp/` (hand-written, with
the program listings in the trace file so the review reads them) and
`corpus/seccomp-controls/`; `evaluator/generate.py` gains a `seccomp`
profile for the generated set.

Hand-written (about 45 traces), one per arm:

- install: the `RET ALLOW` singleton; the canonical prologue alone; the
  NULL program; length 0 and 4097, and a 768-instruction program as the
  long install (4096 is out of reach: stream W measured about 250
  comparison records per classic instruction at an install, KCOV's switch
  instrumentation writing one per case, against the 262,143-entry area,
  which overflows at 1024; 768 is the safe size, X); a bad `sock_fprog`
  pointer and a bad instruction pointer (the two `-EFAULT` arms, `bad`);
  each flag-mask arm and each invalid flag combination; `prctl` with mode
  0, 3 and 255;
- checker: one trace per `-EINVAL` arm of 2.5 (unknown code, `DIV|K` 0,
  `MOD|K` 0, `LSH|K` 32, `ST` 16, `JA` past the end, `jt` past the end,
  `jf` past the end, a last instruction that is not `RET`, an unknown
  ancillary offset, a known ancillary offset rejected by seccomp, a
  misaligned CTX load, a CTX load at 64, `LD|H|ABS`, `LDX|MSH`, `MOD|X`,
  a load of an unstored cell, a load of a cell stored on one path only);
  and the `LEN` rewrite with a program that returns `ALLOW` iff `LEN ==
  64`;
- actions: `ERRNO` with data 0, 1, 4095, 4096, 65535; `TRAP` with data;
  `LOG`; `TRACE` (the `-ENOSYS` arm); `KILL_THREAD`, `KILL_PROCESS` and
  action `0x10000` in a child; `ALLOW` on 1000 (`-ENOSYS` from the table,
  cache miss witnessed); in a child, `RET|A` with `A` loaded from an
  argument that is 0 and then one that is `ALLOW`, `DIV|X` with `X` zero
  (the translation's guard: result 0, `KILL_THREAD`, `SIGSYS`), and with
  `X` non-zero (`MOD|X` and `MOD|K` never run: `seccomp_check_filter`
  lists `DIV` and not `MOD`, 2.5, so they are checker arms, measured by W);
- chains: two filters where the older kills and the newer allows (the cache's
  `bitmap_copy` arm, the most-restrictive rule); the reverse; two with equal
  actions and different data (the tie rule); a third filter; four
  768-instruction filters (the budget's walk over the chain, a probe through
  four programs); and the budget itself through the prefill fixture (5) [USER
  2026-10-12: queued]: recorded installs alone cannot reach it (32768
  installed eBPF instructions are at least 42 installs of 768, at about 0.48
  MB of console each in the cheapest shape; X measured 5.78 MB for 12 and the
  16 MB limit at 43), so eight prefilled copies (31992 with the walk's
  penalty) leave 776, and `s_budget_enomem`'s 772-instruction install (779
  eBPF: the arch test's negative constant costs the conversion one more,
  `filter.c:755-760`) is `-ENOMEM` at 32771, while `s_budget_edge`'s 768 (775)
  fits at 32767 and the next is refused at 33546; the kernel's records at
  `seccomp.c:925` read (0x8000, 0x8003), (0x8000, 0x7fff) and (0x8000, 0x830a)
  (X, on sc2). The compare's operand, Linux's `total_insns` against the
  mirror's, is the fixture's acceptance evidence;
- modes and privilege: strict in a child then an allowed call (`exit`),
  then a killed one (`SIGKILL`); strict after filter (`-EINVAL`, the
  child's `strict_ret`); not filter after strict: the `seccomp` call
  itself is killed before `seccomp_may_assign_mode` runs, and 317 is
  outside the probe set, so the arm is unexercised (9.3); `capdrop` then
  install (`-EACCES`), then
  `set_no_new_privs` then install (0); the `prctl` argument arms;
  `get_seccomp` before and after; `get_action_avail` for each action and
  one unknown; `get_notif_sizes`;
- the uretprobe exception: a filter killing 335, then a child probe of
  335, observed as the child's `ret = -ENOSYS` from the call itself and
  never as `SIGSYS`: the cache answered before the program;
- mixed: a filter, then eventfd and pipe ops, to witness the cache path
  on harness calls and the file table unchanged by seccomp.

Generated (about 300 traces, seeded): (g1) **checker fuzz**, 1-24 random
`sock_filter` words over the whole code space, install only, for the
checker's verdict; (g2) **behaviour**, 1-3 chained filters from the
prologue plus a random body over the seccomp language (loads of `nr`,
`arch`, `args[k]`; ALU with immediates and `X`; stores and loads of
cells after stores; forward jumps; `RET` with a random action, canonical
or not, and random data), then 2-6 probes over the probe set with random
arguments, `self` where the validator's scan allows and `child`
otherwise, at most three child probes per trace; (g3) **mixed**, g2
interleaved with non-blocking eventfd and pipe ops. A child probe costs
about 4.3 MB of the guest's console in the check's comparison mode (the
parent's `clone` and `wait4` records and the child's streams; measured on
sc2 by X: three probes in 13.1-13.6 MB; W's 1.1 MB was the Linux-only
harness's), and an install about 0.6 KB per classic instruction, so
`evaluator/check.py` chunks the suites by an estimated console cost
(`seccomp_console_cost`, budget 12 MB per guest), the 16 MB limit
unchanged and its split the backstop. No `ERRNO` data is one of the errnos
the harness treats as its own infrastructure failing (4, 12, 23, 512-516,
`harness/linux.py`).

Controls (`corpus/seccomp-controls/`): `tsync` and `new_listener` flags,
a `USER_NOTIF` action, a filter loading offset 8, each expected to stop
`unsupported` at the named site while the kernel runs it (`tsync` on a
single thread is a successful no-op in the C, `seccomp_can_sync_threads`
:490 and `seccomp_sync_threads` :597 skipping the caller: its exclusion is
a scope choice honouring the brief, two decisions away if wanted later);
and a harness unit test that the validator rejects `self` after a filter
that may kill, `strict` in the trace process, and `seccomp_child` with a
network fixture (`harness/test_trace.py`, W). `scripts/seccomp-controls.py`
runs each control alone and expects the `unsupported` stop at its site.

One sentinel, under the at-most-one rule: `cache-forgets-prev` replaces
`bitmap_copy` by `bitmap_fill` in `seccompCachePrepare`, so a newer filter
that is const-allow for a number hides an older filter's kill. The
two-filter chain trace catches it as a data mismatch (`ALLOW` against
`SIGSYS`) and a control-flow mismatch (the cache-hit arm against the
loop); nothing else in the mirror would.

## 8. Evidence: what pays for itself

Under `AGENTS.md` "Gates and speedbumps":

- gates: the build and unit tests, which here include a Lean-side
  executable check that for every corpus program `classicRun p d` equals
  `MiniInterp.run (translate p) d` on the trace's probes (the executable
  shadow of 4.6's statement 4: cheap, and it localises a translation
  defect to the translator before the kernel is consulted); the full
  differential check on the new oracle, all suites, including the
  regression claim that the existing corpora are unchanged by listing
  `kernel/seccomp.c` and the three signal functions; the kernel identity;
- speedbumps: the sentinel above; the control suite;
- the one-off mutant for the kind-309 instrument (3.3), under the rule
  for a new instrument on the trust surface: the `jt == 0` arm of the
  translation emitting `JLE` for `JGE` (`filter.c:761-779`), which the behavioural
  check catches only when a probe hits `A == k` and the record catches at
  the first install; run once, reported in the claim commit, deleted.

The claim point's commit message carries the counts and the user's
signoff; no bundle, no narrative.

## 9. Out of scope (fail-noisy), and why

### 9.1 Stops the validator and the mirror make

| What | Where it stops | Why |
| --- | --- | --- |
| threaded `TSYNC` (a second thread to synchronise) | not expressible; the mirror's thread walks stop `unsupported` on another thread | single-task domain; `TSYNC` and `TSYNC_ESRCH` on the one-task group are in scope since the pre-release review (`s_tsync_single`) |
| `NEW_LISTENER`, `WAIT_KILLABLE_RECV`, `USER_NOTIF` | validator; mirror `unsupported` at `seccomp_set_mode_filter` / `__seccomp_filter` | a listener file and a blocking protocol |
| `TRACE` with a tracer | mirror `unsupported` at the `ptrace_event_enabled` cut | no tracer in the fixture; the no-tracer arm is in scope |
| a CTX load of offsets 8..15 without a kind-312 record | engine `unsupportedRead` | only in a record-free run; `instruction_pointer` is recorded since the pre-release review (3.2) |
| strict mode in the trace process | validator | the process could not report (6.2) |
| a second thread | not expressible | single-task domain |
| a file operation in the child | runner `invariant` | the child has no modelled file table (4.1) |

### 9.2 Not modelled

`seccomp_do_user_notification` and the notifier (`:1148-1916`), the
listener file operations, `seccomp_sync_threads`, `is_ancestor`,
`seccomp_can_sync_threads`, `get_nth_filter` and the `ptrace` filter
readers (`CHECKPOINT_RESTORE` unset), the sysctl writers, `audit_seccomp`,
`arch_seccomp_spec_mitigate`, `disable_TSC`, the `MODE_DEAD` and
`do_exit(SIGSYS)` arms (2.1, 2.2), `bpf_check_basics_ok`'s length arms
(unreachable after `seccomp_prepare_filter`'s own test), the
`convert_bpf_extensions`, `convert_bpf_ld_abs`, `MSH` and `LEN` arms of the
translation (unreachable after `seccomp_check_filter`), the classic JIT
(a weak no-op), `bpf_prog_select_runtime`'s JIT and offload arms
(`BPF_JIT` unset), the release walkers (an environment effect, 2.8),
signal delivery (an environment effect, 2.2), `prctl`'s dispatch and
`capset` (data-only ops, 6.3), `dup_fd` and the rest of `clone` (3.1).

### 9.3 Modelled but unexercised, and said so

The `-ENOMEM` arms of allocation sites 2, 4, 5 and 10; `bpf_convert_filter`'s
`pass > 2` arm (the C's comment says the second pass must converge); the
`WARN_ON` fall-off in `seccomp_is_const_allow` (impossible for a checked
program: it ends in `RET`); `seccomp_may_assign_mode`'s refusal of a
filter after strict (:437-445: under strict the `seccomp` call is killed
before it, and 317 is outside the probe set). Each is a decision the mirror
emits and no trace witnesses; the check's `known_gaps` does not list them,
since they are modelled. The path budget's `-ENOMEM` (:925) left this list
with the prefill fixture (5, 7).

## 10. Risks

1. **The child probe's plumbing** (6.2): a second KCOV descriptor, a
   shared mapping, a shared result page, `RLIMIT_CORE`, `exit` versus
   `exit_group` under strict. About 80 lines of guest C with several ways
   to be subtly wrong; step 0 builds it first, on a scratch kernel. The
   fallback, if the shared mapping does not survive the child's death as
   `kcov_mmap`'s `vm_insert_page` (`kernel/kcov.c:508`) and the reset at
   exit suggest it does, is a child probe without coverage, declared as an
   unwitnessed op in `kcov.json`; the data check of the kill still holds.
2. **The signal extension's delivery side** (2.2): unlisted functions of a
   listed file in the `TRAP` window. If step 0 finds a span line of a
   listed decision covered by `get_signal` or `rt_sigreturn`'s path, the
   line is modelled or declared in `known_gaps`; the mirror never absorbs
   it.
3. **The child's representation** (4.1): a second `Task` and a `current`
   selector through `Seccomp/*` and `Signal.lean`. It is the interface
   commit's largest change and the one every stream depends on, which is
   why it is in step 1 and not in V.
4. **The engine subset.** `MiniInterp` must match the interpreter on the
   emitted opcodes (shift masking, 32-bit wrap, the zero-extension
   invariant, the negative-immediate temporary). g2's random ALU bodies
   are the test; a disagreement shows as a data mismatch on a probe with
   the translation's decisions all witnessed and its instructions all
   recorded, which points at the engine.
5. **`TRAP`'s return value** is an x86 register fact (2.2); if the
   measurement shows anything but the call number, it is excluded as an
   operand rather than modelled.
6. **Long filters.** The budget traces walk 4096 instructions through
   three checker passes and two conversion passes, and `seccompCachePrepare`
   emulates such an `orig_prog` 463 times; the check's cost is bounded by
   distinct pairs (4.2), but the mirror's emission size and Lean run time
   are worth one measurement at step 0 beside the three-filter trace.
   The 768-instruction ceiling per install is the comparison child's
   record area (about 250 comparison records per classic instruction,
   stream W), an instrumentation limit, not a semantic one; a sparse
   4096-instruction single filter stays **deferred** (pre-release review
   finding 11): the harness runs both children for every trace and the
   comparison child reports `empty_or_full_kcov` at that size, so a
   Linux-only observation with the kind-309 bytes compared offline needs a
   PC-only observation mode the harness does not have, a harness change
   outside the scope-wording task; the translation of long programs is
   exercised by the 768-instruction installs and the 3990-instruction
   prefill program's offline translation (`s_budget_*`).
7. **Config.** `CONFIG_SECCOMP=y` is additive (2.1, 6.3); the regression
   claim on the existing corpora is the evidence. It is the first
   behaviour-bearing config change since the 2026-10-07 rule; the user
   opened the case on 2026-10-12 and the signoff is section 16's.

## 11. Execution plan

| Step | Stream | Work | WU |
| --- | --- | --- | --- |
| 0 | coordinator | A scratch build with `CONFIG_SECCOMP=y` (not the oracle; under `capped`); the child-probe plumbing prototyped in the guest against it; one child probe's coverage read for `dup_fd` span lines and the window's end; one `TRAP` trace's coverage read for delivery-side span lines in `kernel/signal.c`; `TRAP`'s return value; the mirror's emission size and run time on a three-filter trace and on a 4096-instruction install. | 0.07 |
| 1 | coordinator | The interface commit: opcodes 30-34 named, `AllocSite` and `HiddenSite` ids in 400-419 (the kind-305 sites of 3.1 and the kind-309 site; 200-219 is taken by `Worker.sectionId` from index 15), `SeccompState`, the `Task` fields, `Kernel.seccompFilters` and `Kernel.child` with the `current` selector and `Signal.lean`'s target as a parameter, the repeatable marks for the per-instruction and per-number decisions, `cut_functions`, the files and functions of 6.3, the data-only op list, the `seccomp_child` fixture flag and its exclusivity in the interface table, `CONFIG_SECCOMP=y` in `kernel/config-x86_64-net-choice`. | 0.05 |
| 2 | U | `Classic.lean`, `Translate.lean`, `Engine.lean` with `MiniInterp` and `classicRun`; the Lean-side equality check of 8; unit tests on the hand-written rejection set. | 0.25 |
| 3 | V | `Filter.lean`, `Syscalls.lean`, the per-op `secureComputing` pre-step in dispatch, the child's creation and exit effect and the `TRAP` delivery effect in the runner and `Env.lean`, the observations; the `Signal.lean` extension of 4.5 (about 0.1). Depends on 1 and U's types (not U's bodies). | 0.4 |
| 4 | W | The five operations, both probe modes, the handler, descriptor 8, `RLIMIT_CORE`, `capset`, the `bad` pointers; `trace.py` fields and the validator rules of 6.1; `linux.py`'s fixture row; the contract; `kcov.json`; the kind-309 hook in `gen-choice-stream.py`; the data-only exemption in `check.py`; the oracle rebuild shared with epoll and its identity. | 0.25 |
| 5 | X | `seccomp-corpus.py`, the generated profile, the controls, the sentinel, the one-off mutant of 8, the claim point: full check on the new oracle, controls, sentinel, then one signoff. | 0.18 |

About 1.2 WU in all, above the scout's 0.5-0.7 band by the translation
mirror, the child and the signal chain, none of which the scout counted.
U and W run in parallel after step 1; V stubs the engine with `classicRun`
until U lands and starts its signal extension first, since nothing else
in V needs it finished; X starts when V passes the hand-written set on the
scratch kernel and finishes on the oracle. The oracle rebuild is the one
shared with epoll's kind-308 record, after both designs are audited
(`docs/decisions.md`, 2026-10-12).

## 12. File ownership

| Stream | Files |
| --- | --- |
| U | `Leanux/Seccomp/Classic.lean`, `Translate.lean`, `Engine.lean` (new); `tests/Seccomp*.lean` |
| V | `Leanux/Seccomp/Filter.lean`, `Syscalls.lean` (new); `Leanux/Kernel/Signal.lean` (the extension); `Leanux/Runner.lean` (dispatch, the child, the observation); `Leanux/Env.lean` (the two effects) |
| W | `harness/guest.c`, `harness/trace.py`, `harness/linux.py`, `contracts/trace-v1.md`, `correspondence/kcov.json`, `evaluator/check.py` (the data-only list), `kernel/config-x86_64-net-choice`, `kernel/identity-*.txt`, `kernel/patches/gen-choice-stream.py` (kind 309) |
| X | `scripts/seccomp-corpus.py`, `corpus/seccomp/`, `corpus/seccomp-controls/`, `evaluator/generate.py`, the sentinel and the one-off mutant scripts |
| coordinator | `Leanux/Kernel/Defs.lean` and `Decision.lean` (the interface commit), `docs/2026-10-11-interface.md` (the fixture exclusivity), `docs/decisions.md` |

## 13. Decisions

Tactical, under the user's standing delegation of 2026-10-12, taken by the
coordinator on the audit's recommendation [AGENT, coordinator 2026-10-12],
to be entered in `docs/decisions.md` with the integration:

1. `TRAP` in scope through a `SIGSYS` handler (2.2, 6.2 rule 3), at the
   cost of the signal extension (about 0.1 WU): it is the one action
   besides `ERRNO` that real sandboxes use for emulation.
2. The child probe with a second KCOV descriptor at 8 (6.2 rule 2) rather
   than unwitnessed child probes or a `CLONE_VM` child: the only way to
   witness the kill arm, and the reserved descriptor follows the fixture's
   pattern.
3. Strict mode in scope, child-only (2.9): the original seccomp, and the
   `may_assign_mode` arms need it.
4. `TRACE` without a tracer in scope (2.2), a widening of the brief's
   exclusion list by one `if`; the tracer arm stays out.
5. The engine contract as a typeclass with `MiniInterp` (4.4) rather than
   the classic semantics on the modelled path: the translation stays on
   the modelled path and the JIT project has a drop-in point.
6. The probe set and the prologue rule (6.2 rule 1); the wire mapping and
   the sub-commands of ops 32 and 34 (6.1); the validator's conservative
   kill scan (6.1); the sentinel (7); the uretprobe control (7).
7. Ops 32 and 33 as data-only operations rather than listing
   `kernel/sys.c` (6.3).
8. The kind-309 record of the translated program in its per-instruction
   shape (3.3): record-only, under the approved class, landing with the
   per-merge signoff and the new identity, with its one-off mutant (8).

The user's, as one case (section 16): the config change (`CONFIG_SECCOMP=y`
with `SECCOMP_FILTER` following; already opened by the user's decision of
2026-10-12, restated with what it selects) and the widening of the P
design's decision P9 to the generation of an unblocked `SIGSYS` (2.2, 4.5).

## 14. Audit [AGENT, independent audit 2026-10-12]

An independent read of sections 1-13 against `.deps/linux` (6.12.110),
`kernel/config-x86_64-net-choice`, `correspondence/kcov.json`,
`evaluator/check.py`, `harness/guest.c`, `harness/linux.py`,
`kernel/patches/gen-choice-stream.py` and `Leanux/Kernel/{Defs,Signal}.lean`.
Nothing was built or run. Severities: **high** blocks the plan as written,
**medium** changes a decision or a stream's scope, **low** is a correction
the builder makes in passing. The body above is unrevised; the findings
are for the v2 revision.

### 14.1 Kernel paths (C)

- **C1 (high). The child's `seccomp_filter_release` is not in the child's
  window.** `do_exit` calls `kcov_task_exit` at `kernel/exit.c:894`, before
  `exit_signals` (:902) and `seccomp_filter_release` (:904). The child's
  KCOV is disabled when the release runs, so 6.2 rule 2's claim that "the
  exit's `seccomp_filter_release` (2.8) is in it" is false, and
  `seccompFilterRelease`'s decisions (4.5) would fail "outcome not
  witnessed" on every child probe. The same ordering puts the child's
  `exit_files` (:949) and `do_notify_parent` outside the window, which is
  welcome: the child's file-table teardown is never witnessed. Revision:
  apply the release's count effects (2.8) as an environment effect of the
  child's exit (`Leanux/Env.lean` or the runner), with no decisions
  emitted; keep `getSeccompFilter` as a modelled, witnessed step of the
  parent's `clone`.
- **C2 (high). `TRAP` and the kills run the anchored signal chain, which
  the existing mirror stops `unsupported` on.** `kernel/signal.c` is a
  listed file, and `send_sig`, `send_sig_info`, `do_send_sig_info`,
  `send_signal_locked`, `__send_signal_locked`, `prepare_signal`,
  `complete_signal` and `__sigqueue_alloc` are listed decision functions
  (the P design's SIGPIPE chain, `Leanux/Kernel/Signal.lean`, mirrored
  "down to the pending set" with an unblocked signal, a waking thread and
  handler dispositions `unsupported`). `force_sig_seccomp`
  (`kernel/signal.c:1855`) enters that chain through
  `force_sig_info_to_task` for every `TRAP` (trace process or child) and
  for every `KILL_*`/`default` arm in the child; `SIGSYS` is unblocked with
  a handler (`TRAP`) or fatal (`KILL`), so `complete_signal` reaches
  `wants_signal`/`signal_wake_up`, the current `unsupported` stop, and the
  check additionally fails "Linux ran a decision function the mirror
  reported nothing in". Section 6.3 lists no signal.c function and 3.1 omits
  the `sigqueue` slab allocation (`__sigqueue_alloc`, already
  `AllocSite.sigqueueAlloc`), which every `TRAP`/`KILL` makes. Revision:
  stream V extends `Signal.lean` with `force_sig_info_to_task` (the
  blocked/ignored/`SIG_DFL` test, `HANDLER_EXIT` and `SA_IMMUTABLE`, the
  `sigdelset`/`recalc_sigpending_and_wake` arm), `complete_signal`'s
  wake arm and `signal_wake_up_state`, lists them in 6.3, adds
  `sigqueueAlloc` to the seccomp traces' armed ranges, and 13.1's "ten
  lines" becomes about 0.1 WU. The delivery side (`get_signal`,
  `dequeue_signal`, `signal_setup_done`, `set_current_blocked` on
  `rt_sigreturn`) is in the listed file but unlisted; the check tolerates
  it unless it covers a span line of a listed decision ("span lines covered
  by an unlisted function"). Step 0 measures that on one `TRAP` trace; a
  collision is modelled or declared in `known_gaps`, not absorbed.
  Widening the P design's user decision P9 (signals down to the pending
  set) is the user's call (14.5).
- **C3 (medium). The uretprobe control cannot observe `SIGILL`.**
  `CONFIG_UPROBES` is not set (absent from the config; `arch/x86/kernel/
  Makefile:154` builds `uprobes.o` only under it), so `sys_uretprobe` is
  `COND_SYSCALL` (`kernel/sys_ni.c:394`) and call 335 returns `-ENOSYS`
  when allowed. The exception itself is real (`seccomp_uprobe_exception`,
  `seccomp.c:736-745`; `mode1_syscalls` :1050) and `__NR_syscalls` is 463
  (`mseal` 462 is the last entry; there is no `uprobe` 336 on this
  branch). The control's expectation in 7 becomes `-ENOSYS` against the
  filter's `SIGSYS`, a cleaner witness of "the cache answers before the
  program" than `SIGILL` would have been.
- **C4 (medium). Ops 32 and 33 have no anchored coverage before a mode is
  set.** `PR_SET_NO_NEW_PRIVS`/`PR_GET_NO_NEW_PRIVS` are entirely in
  `kernel/sys.c` (:2632-2641; `task_set_no_new_privs` is a `sched.h`
  inline) and `capset` is in `kernel/capability.c`; neither file is listed,
  and the check fails an operation with "no coverage in anchored files"
  and "no model decision". 6.3's "the seccomp arms are witnessed in
  `kernel/seccomp.c`" holds only for `PR_SET_SECCOMP`/`PR_GET_SECCOMP`.
  Revision: either list `kernel/sys.c` with `prctl`'s switch as a decision
  (its arms are KCOV points) or declare ops 32 (nnp sub-commands) and 33
  coverage-free in `control_flow` the way `wg_flood`/`wg_batch` are
  special-cased, with the data check as their only evidence. The second is
  cheaper and honest; record it as a declared unwitnessed op in
  `kcov.json`.
- **C5 (low). Allocation sites 2 and 10 are unrecordable by construction,
  not by measurement.** The kind-305 hook tests the allocator entry's own
  return address against the armed ranges (`gen-choice-stream.py`
  :1060-1078); for `__vmalloc` that address is inside `mm/vmalloc.c`, as
  are the `vm_struct`, `vmap_area` and page-array slab allocations
  `__vmalloc` makes on the way. Step 0 need not measure this; the design's
  fallback (unrecorded, assumed to succeed, `-ENOMEM` arms modelled but
  unexercised) applies from the start, and risk 1 is settled. Sites 4-5
  are the same case.
- **C6 (low). Small factual slips.** `check_load_and_stores` is an
  intersection over incoming edges: it rejects a load of a cell *some*
  path has not stored (`masks[target] &= memvalid`), not "no path has
  stored" (2.5). `seccomp_filter_release` (:572-585) has no early return
  for a task without a filter: it takes `siglock`, clears the head and
  walks nothing (6.3's "return at their first test" is wrong, harmless:
  outside every window and after `kcov_task_exit`).
  `__secure_computing_strict` writes `mode = SECCOMP_MODE_DEAD` before its
  `seccomp_log` and `do_exit(SIGKILL)` (2.9 omits it). `do_seccomp`
  requires zero flags for `GET_NOTIF_SIZES` as well as `GET_ACTION_AVAIL`
  (2.4). By my count `chk_code_allowed`'s table has 49 entries and
  `seccomp_check_filter` passes 38 codes besides its three rewrites (2.5
  says 52 and 39); the builder recounts. `alloc_percpu_gfp` sites are at
  `core.c:114` and `:151`. `ERRNO` with data 0 returns 0 with no error:
  worth a hand-written trace beside 1 and 4095.
- **C7 (verified, no change).** Everything else in section 2 checked
  against the source: `__secure_computing`'s three live arms and the
  uninstrumented entry (`kernel/entry/common.c:55`, `Makefile:7`); the
  `__seccomp_filter` arms and `skip`; `ACTION_ONLY` as `s32`, strict
  less-than so the newest filter wins ties; the never-cached range test;
  `seccomp_set_mode_filter`'s three early `-EINVAL`s and the
  `prepare_user_filter`-before-locks order; `seccomp_prepare_filter`'s
  order (length, `-EACCES`, `kzalloc`, `bpf_prog_create_from_user`, the two
  `refcount_set(1)`); the path budget with the four-instruction penalty on
  eBPF lengths and `MAX_INSNS_PER_PATH` 32768; `bpf_prog_create_from_user`
  and `bpf_prepare_filter`'s sequence including `bpf_prog_store_orig_filter`
  before `seccomp_check_filter`'s rewrite; `bpf_prog_realloc`'s page test
  (:257); the weak `bpf_jit_compile` (:3069); the native-only cache check
  (`arch/x86/include/asm/seccomp.h`, `CONFIG_COMPAT` off); `copy_seccomp`'s
  single `refs`/`users` increment and the child's cleared KCOV;
  `kcov_reset` clearing `kcov->t` and restoring `KCOV_MODE_INIT` so a later
  child can `KCOV_ENABLE` the same descriptor (`-EBUSY` otherwise); the
  `TRAP` return value (`syscall_rollback` leaves `orig_ax` in `ax`, and
  `do_syscall_64` leaves `ax` alone for `nr = -1`); `force_sig_seccomp`'s
  fields; the strict allowlist. SIGCHLD to the parent is default-ignored
  and dropped in the child's `do_notify_parent` (child context, outside the
  window), so the parent's `wait4` delivers nothing.

### 14.2 Mirror and seam (M)

- **M1 (medium). The decision volume of 2.6 dissolves in the check's own
  semantics; keep the emulation on the modelled path.** The check compares
  the *set* of (decision, outcome) pairs per operation and tolerates
  repeats only for decisions marked `repeatable`
  (`Leanux/Kernel/Decision.lean:1868`; `control_flow`'s "decision reported
  more than once"). Every per-instruction decision of 4.2-4.3 (the checker
  walks, the two conversion passes) and every per-number decision of
  `seccompCachePrepare` repeats within one install, so they must be
  `repeatable` regardless of volume; the design does not say so. Once they
  are, the mirror may emit each pair once per operation (dedupe at
  emission), the Python intersection is set-sized, and risk 3's "cut with
  bitmap as data" fallback is unnecessary. The 463 runs stay in Lean,
  where they are cheap. KCOV's side is not a concern either: `CAPACITY` is
  1M entries (`guest.c:46`), and even the 4096-instruction budget traces
  stay well under it.
- **M2 (medium). The child needs a representation; `Kernel` has one
  task.** `Kernel.task : Task` is the only task (`Defs.lean:331-372`), and
  `Signal.lean` states "the target is always `current`, the one task". A
  child probe runs `force_sig_seccomp`, `__secure_computing` and strict
  mode in a second task with its own `seccomp`, `noNewPrivs`, `blocked`
  and `pending`. Sections 4.1 and 5 name the child but not where it
  lives. The interface commit (step 1) should add `Kernel.child : Option
  Task` (or a `current` selector), created at the probe from the parent's
  state through `copy_seccomp`'s effects and destroyed at `wait4`, and
  `Signal.lean`'s single-task assumption becomes a `current` parameter.
  This is V's largest structural change and belongs in step 1, not step 3.
- **M3 (low). The engine contract should state the register width
  convention.** The translation emits 64-bit `BPF_JMP`-class comparisons
  (`JGT`/`JGE`/`JLT`/`JLE`/`JEQ`/`JNE`/`JSET`) on registers whose upper 32
  bits are zero because every write to `A`, `X` and `TMP` is an ALU32 or
  `MOV32_IMM` (zero-extending). `MiniInterp` over `UInt32` is correct only
  under that invariant; item 4 of 4.4 should say it, so an external ISA
  model over `UInt64` is checked against the same terms. Likewise the
  `classicRun` reference of 4.6 must define `LSH|X`/`RSH|X` with a count
  of 32 or more as the eBPF does (count masked to 5 bits) and `DIV|X`/
  `MOD|X` by zero as "the program returns 0": statement 4 is false under
  the naive classic reading.
- **M4 (low). The one core.c decision the mirror takes should be named as
  such.** `bpf_prog_realloc` is a cut function (6.3) whose `pages <=`
  test (`core.c:257`) the mirror nonetheless evaluates (3.1, risk 6) to
  decide whether an allocation record is due. With C5 the record never
  comes, so the decision has no witness and no data effect: drop the
  `pages` field, the DWARF constant and risk 6, and treat
  `bpf_prog_realloc` as an allocation step that is assumed to succeed. The
  seam statement of 4.4 ("no decision inside the service is a mirror
  decision") then holds for core.c as a whole.
- **M5 (low). Proof shapes.** Statement 1 (chain monotonicity) also relies
  on the uretprobe exception, since the first filter's bitmap has bit 335
  set whatever the program says; state the exception once for both 1 and
  2. `TSYNC` on a single-threaded task is a successful no-op in the C
  (`seccomp_can_sync_threads` and `seccomp_sync_threads` skip the caller)
  and is the flag every real sandbox sets; the brief's exclusion is
  honoured, but it costs two decisions to bring in later, and the control
  that expects `unsupported` should say that is a scope choice, not an
  impossibility.
- **M6 (verified).** The seam is clean: `kernel/bpf/core.c` and
  `include/linux/filter.h` are unlisted, `seccompRunFilters` is parametric
  in `BpfEngine`, `MiniInterp` rejects anything the translation cannot
  emit, and the engine's only effect is `R0`'s low 32 bits. The classic
  checker and translation are on the modelled path with their decisions,
  which is where the thin layer wants them. The cache's emulation on
  `orig_prog` (pre-rewrite codes) is right.

### 14.3 Evidence (E)

- **E1 (medium). The kind-309 record as specified cannot be carried.**
  `kcov_choice_write` caps a record's payload at `KCOV_CHOICE_MAX_WORDS`
  (5 words, 40 bytes; `gen-choice-stream.py:64, :182`), and records share
  the KCOV area. "Up to 256 instructions" (13.3) is 2 KB. Two shapes fit:
  one record per emitted eBPF instruction (one payload word each, four
  words with header, site and sequence; about 80 per generated install)
  or one record of the eBPF length plus a 64-bit hash of the instruction
  bytes. The per-instruction form keeps the diagnostic local (the first
  differing instruction) and is the one to propose; the hash form is
  cheaper and enough for the gate. Either way the instrument needs its
  one-off mutant under AGENTS.md's rule, with a mutant the behavioural
  check does not catch, e.g. the inverted-condition arm for `jt == 0`
  emitting `JLE` for `JGE` (caught only when `A == k`), run once, reported
  in the claim commit, deleted.
- **E2 (low). The regression claim is right but its reason is not.**
  Listing `kernel/seccomp.c` leaves the existing corpora unchanged because
  `copy_seccomp` and `seccomp_filter_release` run outside every window,
  not because they return early (C6). The claim stands; the sentence
  changes.
- **E3 (low). Step 0 should also time a long-filter install.** The budget
  traces (7) walk 4096 instructions through three checker passes and two
  conversion passes; with M1 the check's cost is bounded by distinct
  pairs, but the mirror's emission size and the Lean run time of
  `seccompCachePrepare` on a 4096-instruction `orig_prog` (463 emulations
  that may each walk far before a `RET`) are worth one measurement beside
  the three-filter trace.

### 14.4 Harness and scope (S)

- **S1 (medium). The syntactic kill rule misses two ways a filter kills
  the trace process.** `RET|A` returns the accumulator, which the program
  may have loaded from `args[k]` or computed; and `DIV|X`/`MOD|X` with
  `X = 0` returns 0 through the translation's guard, and 0 is
  `SECCOMP_RET_KILL_THREAD`. A g2 body with "ALU with immediates and `X`"
  and `X` never set has `X = 0`. Either on a `self` probe kills the trace
  process and the whole batch. Revision: the validator treats any filter
  containing `RET|A`, `DIV|X` or `MOD|X` as potentially killing (child
  only), and the corpus exercises all three in a child so the arms are
  witnessed rather than merely avoided.
- **S2 (low). Observations the child needs that 6.1 lacks.** The child's
  strict call (`SECCOMP_SET_MODE_STRICT` after an inherited filter answers
  `-EINVAL`; 7's "strict after filter") has no field; a strict child that
  leaves through `exit` has a normal exit status, not a `ret` or a
  `signal`. Add `child_setup: {strict_ret}` and `exited: status` to the
  probe's observation.
- **S3 (low). The `-EFAULT` arms need a field.** 7 lists "a bad pointer
  (`-EFAULT`)" for `seccomp_prepare_user_filter`'s copy of the
  `sock_fprog`, and 9.3 calls the instruction copy's `-EFAULT`
  unexercised; op 30's fields express neither (`filter: null` is the NULL
  program pointer, `-EINVAL`). One field, `bad: fprog | insns`, exercises
  both and removes an entry from 9.3.
- **S4 (low). Descriptor 8 is W8's.** `INJECT_FD` is 8 and `PIN_FD` 9 in
  the foreign-creator fixture (`guest.c:79-80`; `linux.py:600`); the
  netlink socket is 7. No seccomp trace uses that fixture, but the
  validator should reject `seccomp_child` with `net_fixture:
  foreign-creator` explicitly rather than by accident of the corpus.
- **S5 (low). The in-window `clone` touches a listed file.** `copy_files`
  → `dup_fd` (`fs/file.c`, unlisted function) runs `copy_fd_bitmaps`,
  `__clear_open_fd` and `kmem_cache_alloc(files_cachep)` inside the
  parent's window. The check tolerates an unlisted function of a listed
  file unless it covers a span line of a listed decision, and the
  allocation is outside the armed ranges; step 0 confirms on one child
  probe (`sane_fdtable_size` and the bitmap copy are the lines to watch).
  Mention it in 6.3 so the next reader does not rediscover it.
- **S6 (verified).** The self-sandboxing rule is sound as stated: the
  harness's calls (glibc's `fork` is `clone` plus two `rt_sigprocmask`,
  `waitpid` is `wait4`, the handler's `rt_sigreturn`, the KCOV `ioctl`s,
  `write`, `mmap`, `exit_group`, and in a mixed trace the pipe profile's
  calls) are all outside the probe set and constantly allowed by the
  prologue, so each is a cache hit; the libc calls none of 102, 104, 107,
  108 on its own. The `invariant` stop of 4.5 is the right backstop. The
  kill-in-a-child plumbing is feasible: KCOV's `ENABLE`/`reset` semantics
  (C7) support re-enabling descriptor 8 per child, the area is the
  kernel's own pages mapped into both processes, and `RLIMIT_CORE` zero
  makes `do_coredump` bail at its limit test with no `0x80` in the wait
  status.
- **S7 (estimate).** With C2 (about 0.1 WU), M2 (about 0.05), the step-0
  additions and E1's rework, the plan is about 1.2 WU rather than 1.0;
  the scout's 0.5-0.7 band did not count the translation mirror, the
  child, or the signal chain.

### 14.5 Which decisions are the user's (D)

- **User's, by the oracle-change rule:** 13.7 (`CONFIG_SECCOMP=y`,
  behaviour/config class; already opened) and 13.3 (a kernel record, even
  record-only; per-merge signoff), the latter re-posed in E1's shape.
- **User's, by precedent:** widening the P design's decision P9 (signals
  mirrored down to the pending set) to handler delivery and fatal signals
  (C2). It is small and the design cannot proceed without it, so it goes
  in the same signoff as 13.7.
- **Tactical, under the standing delegation (record as [AGENT]):** 13.1
  (`TRAP` through a handler, now with C2's cost), 13.2 (the child probe on
  descriptor 8), 13.4 (strict mode, child-only), 13.5 (`TRACE` without a
  tracer), 13.6 (the typeclass with `MiniInterp`), and the five listed at
  the end of 13, plus S1's wider kill rule and C4's coverage-free ops.
  Nothing in 13.1-13.6 changes a trust surface; each is the thin layer's
  natural reading of the C.

### 14.6 Verdict

Sound at the seam and in the kernel reading; not yet buildable at the
boundaries it crosses into already-anchored code. C1 and C2 would fail the
first child probe and the first `TRAP` on the scratch kernel; C4 the first
`prctl` op. All three have mechanical fixes that fit the existing
instruments. With those, M1-M2 settled in the interface commit, S1 in the
validator, and 13.3 re-posed per E1, the plan is a credible 1.2 WU and
streams U and W can start before V's signal extension lands.

## 15. Audit response [AGENT, fork of the coordinator, v2]

Each finding of section 14, what was verified and what changed. Every
corrected line was re-read in `.deps/linux` (6.12.110), the oracle config
and the harness; the audit's own line numbers were checked too (two are
adjusted below).

- **C1 (high), confirmed.** `kcov_task_exit` at `kernel/exit.c:894`,
  `exit_signals` :902, `seccomp_filter_release` :904, `exit_files` :949.
  2.8 and 6.2 rule 2 now say no window contains the release; it is an
  environment effect of the child's exit (5: one `users` and one `refs`
  decrement on the head, the child dropped at `wait4`); the four release
  walkers are removed from 6.3's function list and from 4.5, and listed in
  9.2; `getSeccompFilter` stays witnessed in the parent's `clone`.
- **C2 (high), confirmed.** `force_sig_info_to_task` is `signal.c:1328-1363`
  (the audit's 1855 is `force_sig_seccomp`); `complete_signal` :994-1066,
  `wants_signal` :977-992, `signal_wake_up_state` :759-774; the eight
  listed signal functions and `Signal.lean`'s stops at :23-26, :110, :115,
  :142. 2.2 gains the signal-chain paragraph with each arm read; 4.5 the
  extension (new `forceSigInfoToTask`, `completeSignalWake`,
  `signalWakeUpState`; the real-siginfo and unblocked arms replaced); 6.3
  the three functions; 3.1 site 12 (`__sigqueue_alloc`, armed); 6.2 rule 3
  the cost (about 0.1 WU); step 0 measures the delivery side on one `TRAP`
  trace (risk 2). The P9 widening is the user's (16).
- **C3 (medium), confirmed.** `UPROBES` absent, `arch/x86/kernel/
  Makefile:154`, `kernel/sys_ni.c:394`. The uretprobe control (7) expects
  the child's `ret = -ENOSYS`; 2.6 and 6.2 rule 1 say so; `SIGILL` is gone
  from 6.1.
- **C4 (medium), confirmed.** `kernel/sys.c` :2632-2641, `capset` in
  `kernel/capability.c`; neither listed. Chosen: ops 32 and 33 are
  data-only in the check (6.3), beside the `wg_flood`/`wg_batch` cases at
  `check.py:846-858`, exempt from :872 and :892 only; reason given there
  (sixty-arm switch for two arms, and `prctl_get_seccomp` has no branch).
  Decision 13.7.
- **C5 (low), confirmed** against `gen-choice-stream.py:1058-1080` (the
  hook's range test is on the allocator entry's return address). 3.1 marks
  sites 2, 4, 5 and 10 unrecorded by construction; the measurement and
  risk 1 are gone.
- **C6 (low), confirmed and fixed in place.** `check_load_and_stores`'s
  intersection (2.5); the release's lack of an early return (2.8, 6.3);
  `mode = DEAD` in strict (2.9, :1074); zero flags for `GET_NOTIF_SIZES`
  (2.4); the counts are 49 (`chk_code_allowed`, recounted over the whole
  table) and 38 (2.5); `alloc_percpu_gfp` at `core.c:114` and :151 (3.1);
  `ERRNO` with data 0 added (2.2, 7).
- **M1 (medium), confirmed** (`Decision.repeatable`, `Decision.lean:1868`;
  `check.py:885`). 4.2, 4.3 and 4.5 mark the per-instruction and
  per-number decisions repeatable with emission once per operation; the
  volume risk and the "bitmap as data" fallback are gone; step 1 carries
  the marks.
- **M2 (medium), confirmed** (`Kernel.task`, `Defs.lean:366`;
  `Signal.lean:13`). 4.1 specifies `Kernel.child : Option Task`, the
  `current` selector, what the child holds and lacks, and the
  parameterisation of `Signal.lean`; it is in step 1 (risk 3).
- **M3 (low), confirmed** (`core.c:1841-1866`: the `SHT` macro masks a
  register count with 31 for ALU32, and the comment says a JIT must not).
  4.4 term 4 states the zero-extension invariant; term 3 the masking and
  its JIT caveat; 4.6 statement 4 the semantics `classicRun` must use.
- **M4 (low), confirmed.** The `pages` field, the DWARF constant and the
  old risk 6 are gone; `bpf_prog_realloc` is an allocation step below the
  cut (2.4, 3.1).
- **M5 (low), confirmed.** 4.6 states the uretprobe exception once for
  statements 1 and 2; 7 and 9.1 say `TSYNC`'s exclusion is a scope choice.
- **E1 (medium), confirmed** (`KCOV_CHOICE_MAX_WORDS` 5,
  `gen-choice-stream.py:64`). 3.3 re-poses the record as one per emitted
  instruction plus a length record, with the reason (local diagnostics,
  in-order consumption) and its one-off mutant (8: the `jt == 0` arm,
  `filter.c:761-779`). Record-only, under the class approval, with the
  identity at the merge; decision 13.8, not a user ruling.
- **E2 (low).** 6.3's regression sentence now gives the window reason.
- **E3 (low).** Step 0 times a 4096-instruction install (risk 6).
- **S1 (medium), confirmed.** The validator's scan covers `RET|A`, `DIV|X`
  and `MOD|X` (6.1), and 7 exercises all three in a child.
- **S2 (low).** The child record carries `strict_ret`, `ret`, `exited` or
  `signal` (6.1).
- **S3 (low).** Op 30 gains `bad: fprog | insns` (6.1); 7 has both arms;
  9.3 drops the entry.
- **S4 (low), confirmed** (`guest.c:79-80`, `linux.py:600`). 5 makes
  `seccomp_child` and a network fixture exclusive, the validator rejects
  the pair, and the interface table carries it (12, the coordinator's).
- **S5 (low), confirmed** (`fs/file.c:314`, :295, :56). 6.2 rule 2 names
  `dup_fd` in the parent's window; step 0 reads one child probe for it.
- **S6, S7, C7, M6.** No change; the estimate is 1.2 WU (11).
- **D.** 13 records 13.1, 13.2, 13.4, 13.5, 13.6, the tactical items, the
  kill scan, the data-only ops and the record's shape as the
  coordinator's; the config change and the P9 widening go to the user as
  one case.

## 16. The user's case

**Approved** [USER 2026-10-13]: both rulings below, recorded in
`docs/decisions.md`. The oracle is rebuilt with `CONFIG_SECCOMP=y` at phase 2b
of stream X; the P9 widening is stream V's signal extension (4.5).

For the user [the paste]:

> Two rulings in one, for the seccomp stream (`docs/2026-10-12-seccomp-design.md`, v2).
> 1. Oracle config: `CONFIG_SECCOMP=y`. It turns on `CONFIG_SECCOMP_FILTER=y`
>    as well (`arch/Kconfig`: `def_bool y` under `HAVE_ARCH_SECCOMP_FILTER &&
>    SECCOMP && NET`); nothing else changes (`BPF` is already on; `SECCOMP_CACHE_DEBUG`
>    stays off). On the syscall entry path nothing changes for any existing
>    trace: the slow path runs only when a task has set a seccomp mode, which
>    none of them does; `copy_seccomp` at fork and `seccomp_filter_release` at
>    exit become live but do nothing for a task without a filter and run
>    outside every window. The full differential check on the new oracle, all
>    suites, is the re-validation; it is one rebuild shared with epoll's record.
> 2. P9 widening. P9 [USER 2026-10-06] mirrored `kernel/signal.c` down to the
>    pending set, with an unblocked signal, a waking thread and handler
>    dispositions unsupported. seccomp's `TRAP` and kills generate an unblocked
>    `SIGSYS`, so the widening adds `force_sig_info_to_task` and
>    `complete_signal`'s wake arm for one task (handler or forced default), its
>    sigqueue allocation and the pending flag; delivery (`get_signal`, the
>    handler frame, `rt_sigreturn`) stays an environment effect; stop and
>    continue signals, group delivery, real-time signals and a second thread
>    stay unsupported.

## 17. Phase 2a settling on the scratch kernel [AGENT, stream X, 2026-10-13]

The first differential runs of the three suites on sc2 (`CONFIG_SECCOMP=y`,
not the oracle) settled these, each from the built code's evidence:

- `__seccomp_filter`'s errno cap (:1270): the compiler tests
  `(data & ~0xfff) != 0`; the mirror's operands are the masked data and 0
  (the record is `(0x0, 0x1000)` for data 4096). V had declared a shift.
- `check_load_and_stores`' load test (filter.c:951): `((memvalid >> k) & 1)
  != 0`, the variable the shifted bit and the constant 0 (records `(0x0,
  0x1)` for a stored cell, `(0x0, 0x0)` for an unstored one); V had declared
  a mask test over `(memvalid, bit)`.
- `bpf_convert_filter`'s `DIV|X || MOD|X` guard (:686-687): both compares
  are attributed to the `if`'s first line, so the `MOD|X` decision's line is
  686.
- The child's exit call: the guest leaves with `exit` (60) whenever the probe
  asked for strict mode, whether or not the strict call succeeded
  (`harness/guest.c:1782`); the mirror had chosen by the resulting mode. A
  semantics change in the environment rule (`Env.childExitCall`), from the
  evidence of `s_strict_after_filter_child` (the cache check for 60 recorded
  after a refused strict call).
- Two shared exits declared in `correspondence/kcov.json` (V's open items):
  `bpf_migrate_filter`'s `out_err` block (filter.c:1320 at :1363), covered
  by `bpf_prepare_filter`'s error return on every install
  `seccomp_check_filter` refuses, unless the function's entry (:1263) was
  covered; and `seccomp_get_notif_sizes`'s `return 0` (seccomp.c:2088 at
  do_seccomp :2111), shared with do_seccomp's return on every other
  sub-command, unless the sizes' initialisation (:2079) was covered.
- A four-filter trace of 768-instruction programs is a 65 KB line, over the
  mirror's input limit (`Leanux/Main.lean`); `s_chain_big` holds three.
- The control suite's stop messages, as the mirror words them: the TSYNC arm
  at seccomp.c:2004, the listener arm at :1985, the USER_NOTIF arm at :1326,
  the instruction-pointer read at :425.
