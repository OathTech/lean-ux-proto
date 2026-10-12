# seccomp over a single task — design, 2026-10-12

[AGENT, fork of the coordinator] A design, not a build: no mirror, guest or
kernel code is written here. It follows the kernel scout's profile
(`docs/2026-10-12-kernel-scout.md`, 4.4), the simulation-target review's
rules for cuts and stops (`docs/2026-10-12-simulation-target-review.md`, 3.2
and 4.4), the user's seam of 2026-10-12 (`docs/decisions.md`: the eBPF
engine below `seccomp_run_filters` is a service with a stated ISA contract,
never anchored; the user's separate eBPF JIT project owns that seam) and the
interface allocations on `task/next-targets` (`docs/2026-10-11-interface.md`:
opcodes 30-34, HiddenSite ids 200-219, config `SECCOMP`/`SECCOMP_FILTER`).
Every kernel claim below was read in the configured source, `.deps/linux`
(6.12.110), with the line numbers given; none has been run against a build,
and the current oracle has `CONFIG_SECCOMP` unset, so section 11's step 0 is
a measurement on a local build.

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
- the companions: `PR_SET_NO_NEW_PRIVS`, `PR_GET_NO_NEW_PRIVS`,
  `PR_GET_SECCOMP`, `SECCOMP_GET_ACTION_AVAIL`, `SECCOMP_GET_NOTIF_SIZES`,
  and a capability drop so the `-EACCES` arm is reachable;
- the filter's inheritance across `fork` and its release at exit, because
  the sandboxed child exercises both.

What this adds to the mirror beyond seccomp's own control flow is a
**program checker and translator** (`net/core/filter.c`'s classic BPF
checker and its conversion to eBPF) mirrored with full control-flow
correspondence, and an **engine seam**: the one call that runs the
translated program, `bpf_prog_run_pin_on_cpu` at `kernel/seccomp.c:426`, is
a service with a stated contract (4.4). The mirror ships a minimal
interpreter for the opcode subset the translation emits so that it is
executable today; an external Lean model of the eBPF ISA can replace it
without touching the rest.

Out of scope, fail-noisy (section 9): `TSYNC`, `NEW_LISTENER` and
`USER_NOTIF`, `TRACE` with a tracer, a second thread, filters that read the
instruction pointer, strict mode in the trace process.

## 2. The kernel paths, verified

Configuration facts the paths depend on (`kernel/config-x86_64-net-choice`):
`CONFIG_HAVE_ARCH_SECCOMP=y`, `CONFIG_HAVE_ARCH_SECCOMP_FILTER=y`, `SECCOMP`
unset (:465-467); `CONFIG_BPF=y` (:99), `BPF_SYSCALL` and `BPF_JIT` unset
(:106-107); `AUDIT` unset (:60); `CHECKPOINT_RESTORE` unset (:162);
`IA32_EMULATION` unset (:399), so `CONFIG_COMPAT` is off; `COREDUMP=y`
(:597); `PROC_SYSCTL=y` (:1533). On x86-64 `SECCOMP_ARCH_NATIVE` is
`AUDIT_ARCH_X86_64`, `SECCOMP_ARCH_NATIVE_NR` is `NR_syscalls` (463 in the
built headers, `__NR_syscalls`), and `SECCOMP_ARCH_COMPAT` is undefined
(`arch/x86/include/asm/seccomp.h`). `__NR_uretprobe` is 335.

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
  pass computing the eBPF length, `bpf_prog_realloc` (`core.c:248-276`:
  a fresh `__vmalloc` only when the page count grows, :257), the second
  pass writing the eBPF program, `bpf_prog_select_runtime`
  (`core.c:2527-2580`: no JIT is configured, the interpreter for the
  program's stack depth is selected, `bpf_prog_lock_ro`, `bpf_check_tail_call`
  with no maps), and the free of the saved copy.

Back in `seccomp_set_mode_filter`: `NEW_LISTENER` is out of scope; the
`TSYNC` mutex is out of scope; under `siglock`, `seccomp_may_assign_mode`
(:437-445: a mode already set must be the same mode; strict after filter
and filter after strict are `-EINVAL`), `has_duplicate_listener` (:1917:
false at its first test, no listener), `seccomp_attach_filter`
(:913-963):

- the path budget (:922-926): the new program's **eBPF** length plus, for
  each filter already on the chain, its eBPF length plus 4, must not exceed
  `MAX_INSNS_PER_PATH` (:240; 32768), else `-ENOMEM`;
- `TSYNC` (:929-937): out of scope;
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
argument; `GET_ACTION_AVAIL` (:2053-2075) requires zero flags, copies a
`u32` and answers `0` for the eight known actions, `-EOPNOTSUPP`
otherwise; `GET_NOTIF_SIZES` (:2077) copies three sizes out; an unknown
op is `-EINVAL`.

### 2.5 The checker: `bpf_check_classic` and `seccomp_check_filter`

`bpf_check_classic` (`filter.c:1072-1148`) walks the program once. Per
instruction: `chk_code_allowed` (:981-1045; a table of the 52 classic
codes, anything else `-EINVAL`); then the special cases: `DIV|K` and
`MOD|K` with `k == 0`; `LSH|K` and `RSH|K` with `k >= 32`; `LD|MEM`,
`LDX|MEM`, `ST`, `STX` with `k >= BPF_MEMWORDS` (16); `JA` with `k >= flen
- pc - 1`; the eight conditional jumps with `pc + jt + 1 >= flen` or `pc +
jf + 1 >= flen`; `LD|{W,H,B}|ABS` with `k >= SKF_AD_OFF` (0xfffff000) that
is not a known ancillary load. The last instruction must be `RET|K` or
`RET|A`, and then `check_load_and_stores` (:928-979) runs: a forward
dataflow over the 16 memory cells (`masks` is a `kmalloc_array` of `flen`
halfwords, 3.1) that rejects a load of a cell no path has stored.

`seccomp_check_filter` (`seccomp.c:280-347`) walks the checked program and
rewrites in place: `LD|W|ABS` becomes `LDX|W|ABS` and must have `k < 64`
and `k & 3 == 0`; `LD|W|LEN` and `LDX|W|LEN` become immediate loads of 64
(`sizeof(struct seccomp_data)`); the 39 listed codes pass; everything else
(the half-word and byte loads, `IND`, `MSH`, `MOD`, the ancillary loads
that passed the classic checker) is `-EINVAL`. Note the order: the
original program was already saved by `bpf_prog_store_orig_filter`, so
`orig_prog` holds the un-rewritten codes and the cache's emulation (2.6)
matches on `LD|W|ABS`, not on the rewritten `LDX`.

### 2.6 The cache: `seccomp_cache_prepare` and `seccomp_is_const_allow`

`seccomp_cache_prepare` (:881-898) builds the new filter's `allow_native`
bitmap from the previous filter's (`bitmap_copy`) or from all-ones
(`bitmap_fill`) and, for every number `0..462` whose bit is still set,
clears it unless `seccomp_is_const_allow(orig_prog, {nr, arch})` holds
(:839-873). A bit can only be cleared, never set, so the chain's cache is
monotone by construction (4.6).

`seccomp_is_const_allow` (:762-836) first returns true for
`seccomp_uprobe_exception` (:736: `nr == __NR_uretprobe`, 335), then
emulates the program with one abstract register: `LD|W|ABS` of `nr` or
`arch` loads the constant, any other offset returns false; `RET|K` answers
`k == SECCOMP_RET_ALLOW`; `JA` and the four `|K` conditional jumps follow
the constant; `AND|K` masks; any other instruction returns false; running
off the end is a `WARN_ON` and false. The uretprobe exception means a
filter cannot restrict call 335 on this architecture: the cache answers
`ALLOW` before the program runs, whatever the program says. This is a
semantic fact the mirror reproduces and the theorems (4.6) state.

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
if a mode is set. The child's KCOV is cleared (`kcov_task_init`,
`fork.c:1185`), so a child's calls are not on the parent's coverage.

At exit, `do_exit` (`kernel/exit.c:904`) calls `seccomp_filter_release`
(`seccomp.c:572-585`): the task's head pointer is cleared under `siglock`,
then `__seccomp_filter_orphan` (:534) walks `prev` decrementing `users`
while it reaches zero (waking a listener's poll if any), and
`__put_seccomp_filter` (:543) walks decrementing `refs` and freeing
(`seccomp_filter_free` :526: `bpf_prog_destroy`, `kfree`) while it reaches
zero. For a sandboxed child of a filtered trace process, both walks stop
at the head after one decrement, since the parent still holds it.

### 2.9 Strict mode

`seccomp_set_mode_strict` (:1419-1439): `seccomp_may_assign_mode`, then
`seccomp_assign_mode(current, STRICT, 0)` (`disable_TSC` is a cut). From
then on `__secure_computing_strict` (:1059-1077) allows `read`, `write`,
`exit`, `rt_sigreturn` and `uretprobe` (`mode1_syscalls`, :1048) and kills
anything else with `do_exit(SIGKILL)` after a `seccomp_log` with
`KILL_THREAD`. `exit_group` is not on the list: a strict task must leave
with `exit`.

### 2.10 The companions (`kernel/sys.c`)

`PR_GET_SECCOMP` (:2548) returns the mode. `PR_SET_NO_NEW_PRIVS`
(:2632-2636): `arg2 == 1` and `arg3..5 == 0` or `-EINVAL`;
`task_set_no_new_privs`. `PR_GET_NO_NEW_PRIVS` (:2638-2641): all arguments
zero or `-EINVAL`; the bit. `capset` for the capability drop is below the
cut (`kernel/capability.c`, `security/commoncap.c`): only its effect on
`cap_effective` is mirrored, as a task field.

## 3. Hidden inputs

### 3.1 Allocation sites (kind 305, the existing hook)

The hook records slab allocations (`slab_alloc_node`) and page allocations
(`__alloc_pages_noprof`) with up to four return addresses
(`kernel/patches/gen-choice-stream.py`). One install, in order:

| # | Site | Allocator | Records? |
| --- | --- | --- | --- |
| 1 | `seccomp_prepare_filter` `kzalloc(sfilter)` (`seccomp.c:688`) | slab | yes |
| 2 | `bpf_prog_alloc_no_stats` `__vmalloc(size)` (`core.c:105`) | pages via vmalloc | measurement (step 0) |
| 3 | `bpf_prog_alloc_no_stats` `kzalloc(aux)` (`core.c:109`) | slab | yes |
| 4 | `bpf_prog_alloc_no_stats` `alloc_percpu_gfp(active)` (`core.c:113`) | percpu | no |
| 5 | `bpf_prog_alloc` `alloc_percpu_gfp(stats)` (`core.c:152`) | percpu | no |
| 6 | `bpf_prog_store_orig_filter` `kmalloc(fkprog)` (`filter.c:1156`) | slab | yes |
| 7 | `bpf_prog_store_orig_filter` `kmemdup(filter)` (`filter.c:1163`) | slab | yes |
| 8 | `check_load_and_stores` `kmalloc_array(masks)` (`filter.c:935`) | slab | yes |
| 9 | `bpf_migrate_filter` `kmemdup_array(old_prog)` (`filter.c:1277`) | slab | yes |
| 10 | `bpf_prog_realloc` `__vmalloc` (`core.c:260`), only when the eBPF program needs more pages than the classic one (:257) | pages via vmalloc | measurement |
| 11 | `bpf_convert_filter` second pass `kcalloc(addrs)` (`filter.c:594`) | slab | yes |

Sites 2 and 10 go through `vmalloc`'s page allocator, whose four innermost
frames are vmalloc's own; whether the hook's chain reaches a distinguishing
frame, and whether `vm_area_alloc_pages`' bulk path is seen at all, is
step 0's first measurement. If they are not resolvable, the mirror treats
them like sites 4 and 5: **unrecorded, assumed to succeed**, declared as
such in `AllocSite`'s class, with the `-ENOMEM` arms left as modelled but
unexercised (9.3). A real `-ENOMEM` there would surface as a result
mismatch, which is the fail-noisy outcome. The page-count decision at
`core.c:257` needs `offsetof(struct bpf_prog, insnsi)` (`bpf_prog_size`,
`filter.h:1012-1016`), a build constant read from the DWARF at step 0 and
recorded in `Leanux/Seccomp/Consts.lean`; for every generated program the
classic and eBPF images fit one page and the realloc is the no-op arm.

The sandboxed child's `fork` and `exit` (6.2) allocate nothing in the
anchored files.

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

One hidden value is deliberately not recorded: `instruction_pointer`
(`populate_seccomp_data`, :265). A filter that loads offsets 8..15 passes
the checker (the mirror accepts it too) but makes the engine's input
partial; running such a filter is `unsupported` at the seam (4.4). The
generator never emits those loads; one control does (7).

## 4. The mirror

### 4.1 State (`Leanux/Kernel/Defs.lean`, `Leanux/Seccomp/Defs.lean`)

`Task` gains:

```
seccomp      : SeccompState      -- current->seccomp
noNewPrivs   : Bool := false     -- task_no_new_privs
capSysAdmin  : Bool := true      -- cap_effective ∋ CAP_SYS_ADMIN
sigsysHandler: Bool := false     -- the guest's handler, installed at setup
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
  filters     : List SeccompFilter := []   -- the tree, here a list
```

`seccomp_filter` objects live in `Kernel` keyed by `FilterId` so that a
sandboxed child's inherited chain (2.8) is the parent's objects with
their counts, not a copy. The notifier, lock and wait-queue fields are not
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
step with its `-ENOMEM` arm.

### 4.3 Translation (`Leanux/Seccomp/Translate.lean`)

```
structure BpfInsn where code : UInt8; dst : UInt8; src : UInt8; off : Int16; imm : Int32
structure BpfProg where insns : Array BpfInsn; stackDepth : Nat; pages : Nat; len : Nat

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
convergence test (`pass > 2` is `-EINVAL`). The eBPF length is what the
path budget (2.4) consumes, so the mirror must get it exactly; the
Lean-side check of 8 and a record (13.3) verify it.

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
ISA model can be checked against them:

1. `CTX` reads are `LDX_MEM W` at 4-aligned offsets below 64: offset 0 is
   `nr` as a 32-bit value, 4 is `arch`, 8 and 12 are the two halves of
   `ip` (a stop when `ip = none`), `16 + 8k` and `20 + 8k` the halves of
   `args[k]`, little-endian.
2. The stack is 16 words at `FP - 4 .. FP - 64`, zero before the run;
   `STX_MEM W` and `LDX_MEM W` from `FP` only.
3. ALU32 semantics are the interpreter's (`core.c:1811`): 32-bit wrap;
   shifts by a register mask the count to 5 bits; `NEG` is 32-bit negate;
   `DIV`/`MOD` by a zero register never reach the engine (the translation's
   guard returns 0 before them, 4.3), by a zero immediate never pass the
   checker.
4. Jumps are `off`-relative, 16-bit signed, resolved by the translation;
   `EXIT` returns `R0`; `MOV32_IMM` and `MOV64_REG` as expected.
5. The result is the low 32 bits of `R0`; the engine has no other effect.

The mirror's instance, `MiniInterp`, implements exactly the opcodes the
translation of a seccomp-checked program can emit (about twenty) and
answers `unsupportedInsn` for anything else, so a translation defect
cannot be absorbed by a permissive engine. The user's eBPF JIT project
would provide a second instance over the same `BpfProg`; the mirror's
`seccompRunFilters` is parametric in the instance, and the differential
check runs with `MiniInterp`. No decision inside `run` is a mirror
decision: the C's interpreter is not in `kcov.json`'s `files`, and the
mirror emits none for it.

### 4.5 seccomp proper (`Leanux/Seccomp/Filter.lean`, `Syscalls.lean`)

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
def getSeccompFilter : M Unit                                          -- :971 (fork)
def seccompFilterRelease : M Unit                                      -- :572 (exit)
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
run; this is the mirror's largest per-install decision count (10, risk 3).

### 4.6 Proof-shaped statements

No theorem is written (AGENTS.md). The functions are shaped so these can be
stated over them without restructuring; the Codex spike's charter pattern
applies if the user opens one.

1. **Chain monotonicity.** For a task state `t` and an accepted filter `f`,
   `ACTION_ONLY (runFilters (attach f t) d) ≤ ACTION_ONLY (runFilters t d)`
   for every `d`, where `runFilters` includes the cache. This needs 2 and
   3: the new bitmap is a subset of the old (`bitmap_copy` then clears
   only), and a cache hit on the old chain means every old program answers
   `ALLOW` on `d`, so the new minimum over a superset of programs is at
   most `ALLOW`.
2. **Cache soundness.** `seccompIsConstAllow p d.nr d.arch = true` implies
   `engine.run (translate p) d = ALLOW` for every `args` and `ip`, for any
   engine satisfying 4.4, with the single exception of `nr = 335`, where
   the cache answers without the program: a stated exception, not a
   theorem failure.
3. **Checker soundness.** A program accepted by `bpfCheckClassic ∘
   seccompCheckFilter` terminates within `len` steps (all jumps forward),
   ends at a `RET`, loads only stored cells, reads CTX only in bounds and
   aligned, never divides by a zero immediate.
4. **Translation correctness.** For an accepted program `p` and data `d`,
   `classicRun p d = engine.run (translate p) d`, where `classicRun` is a
   direct semantics of the seccomp-checked classic language (a reference
   function the mirror ships for the executable check of 8, not used on
   the modelled path).

4 is the one the engine seam makes precise: the left side is the mirror's,
the right side is the ISA model's, and the contract of 4.4 is the
interface between the two projects.

## 5. Environment rules (`Leanux/Env.lean`)

- The trace process starts as root with all capabilities, no-new-privs
  clear, mode disabled, no filter; the `SIGSYS` handler is installed by the
  guest at setup, so a `TRAP` never kills the trace process.
- Reserved descriptors: the fixture's 0-7, plus 8 in a trace that declares
  `seccomp_child` (the second KCOV descriptor, 6.2), reported in the
  `LEANUX_FIXTURE` row as today's `reserved` list (`harness/linux.py:600`
  already varies it by fixture).
- `actions_logged` is the kernel default, checked by the fixture row.
- A sandboxed child is a task the mirror creates at the probe and destroys
  at its exit; it has no file table of its own on any modelled path.

## 6. Harness and guest

### 6.1 Operations

Five operations (`harness/trace.py` `FIELDS`, `OPCODES`;
`contracts/trace-v1.md`; `harness/guest.c`), the opcodes allocated in the
interface commit:

| Operation | Fields | Wire (`struct operation`) | Opcode |
| --- | --- | --- | --- |
| `seccomp_install` | `via` (seccomp, prctl), `flags` (names: log, spec_allow, tsync, new_listener, tsync_esrch, wait_killable_recv, or a raw bit for the mask arm), `filter` (list of `[code, jt, jf, k]`, or `null` for the NULL-pointer arm), `len` (optional override, for the length arms) | `a = via`, `b = flags`, `payload = filter`, `value = len` | 30 |
| `seccomp_probe` | `nr`, `args` (six `u64`, default 0), `where` (self, child), `strict` (child only: `null`, seccomp, prctl) | `a = nr`, `b = where ∣ strict << 8`, `payload = args` | 31 |
| `seccomp_prctl` | `cmd` (set_no_new_privs, get_no_new_privs, get_seccomp), `arg2..arg5` (default 0, for the `-EINVAL` arms) | `a = cmd`, `payload = args` | 32 |
| `seccomp_capdrop` | none: `capset` without `CAP_SYS_ADMIN` in the effective, permitted and inheritable sets | | 33 |
| `seccomp_query` | `cmd` (get_action_avail, get_notif_sizes), `action`, `flags` | `a = cmd`, `b = action`, `value = flags` | 34 |

The observation for every op is `struct observation`'s `ret` and `error`
as today. `seccomp_probe` adds: for a `TRAP`, the handler's record
`sigsys: {nr, data, arch}` (the handler stores `si_syscall`, `si_errno`,
`si_arch` into a static the op reads afterwards); for a child probe, the
child's `ret` from a shared page, or `signal` (31 `SIGSYS`, 9 `SIGKILL`,
4 `SIGILL` for the uretprobe control) from `waitpid`. The `ret` after a
`TRAP` is the call number (2.2), predicted by the mirror; step 0 confirms
it is stable, else it becomes a declared exclusion.

The validator rejects: `where = self` once any installed filter of the
trace contains a `RET|K` whose action is `KILL_THREAD`, `KILL_PROCESS` or
non-canonical (a syntactic scan, so the rule is enforced without
predicting the chain); `strict` outside a child probe; `tsync`,
`new_listener`, `wait_killable_recv` flags outside the control suite; a
probe `nr` outside the probe set of 6.2; a filter longer than 4096 outside
the hand-written suite.

### 6.2 The self-sandboxing rule

A filter installed by op 30 governs the trace process, including the
calls the harness makes after it: the fd ops of a mixed trace, `clone`
and `wait4` for a child probe, `rt_sigreturn` after a trap, the KCOV
status ioctls and the `write` of the result at the end. Three rules make
this safe and, more importantly, make the harness's calls invisible to
the engine:

1. **Probe numbers.** A filter in the corpus may restrict only the probe
   set: `getuid` 102, `getgid` 104, `geteuid` 107, `getegid` 108 (in
   range, no arguments, no side effects, result 0 as root, so a filter's
   `args` tests are on values the op controls), `1000` (out of range:
   never cached, `-ENOSYS` when allowed), and `uretprobe` 335 for its
   control (`SIGILL` when allowed, child only). Every other number must be
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
   hold for.
2. **Kills happen in a child.** A probe whose chain may kill runs in a
   sandboxed child: the trace process `fork`s (the child inherits the
   chain, 2.8, with the fork's `get_seccomp_filter` in the parent's
   window), the child enables its own KCOV on descriptor 8 (opened,
   initialised and mapped `MAP_SHARED` by the trace process at setup,
   before descriptors are counted and before the rlimit is lowered, so
   the mapping is visible to both), zeroes the area's count, optionally
   sets strict mode, issues the probe, writes `ret` into a shared
   anonymous page, and leaves with `exit_group` (or `exit` under strict).
   The trace process `waitpid`s and reads the child's area from the
   shared mapping: the window is the child's [probe, exit], and the
   exit's `seccomp_filter_release` (2.8) is in it. `RLIMIT_CORE` is zero
   in the trace process so a `SIGSYS` death attempts no core file. A new
   child can re-enable the same descriptor because `kcov_task_exit`
   resets it.
3. **Traps are caught.** The guest installs a `SIGSYS` handler at setup
   (`SA_SIGINFO`, no `SA_NODEFER` games) that records the three fields;
   with it, `TRAP` returns to the op in both modes.

Strict mode is child-only (rule 2) because a strict trace process could
not read its coverage back (the ioctls are not on the list, 2.9).

The alternative to descriptor 8 is a `CLONE_VM` child whose own KCOV
mapping lands in the shared address space; it avoids the reserved
descriptor at the cost of a separate stack and a clone flag the fixture
has not used. Noted, not chosen (13.2).

### 6.3 Coverage

`correspondence/kcov.json` gains the files `kernel/seccomp.c`,
`net/core/filter.c`; the functions of section 2 (`__secure_computing`,
`__seccomp_filter`, `seccomp_run_filters`, `seccomp_cache_check_allow`,
`seccomp_cache_check_allow_bitmap`, `populate_seccomp_data`,
`seccomp_log`, `__secure_computing_strict`, `seccomp_set_mode_filter`,
`seccomp_set_mode_strict`, `seccomp_prepare_user_filter`,
`seccomp_prepare_filter`, `seccomp_check_filter`, `seccomp_attach_filter`,
`seccomp_may_assign_mode`, `seccomp_assign_mode`, `seccomp_cache_prepare`,
`seccomp_cache_prepare_bitmap`, `seccomp_is_const_allow`,
`seccomp_uprobe_exception`, `has_duplicate_listener`, `seccomp_filter_free`,
`get_seccomp_filter`, `__get_seccomp_filter`, `seccomp_filter_release`,
`__seccomp_filter_release`, `__seccomp_filter_orphan`,
`__put_seccomp_filter`, `do_seccomp`, `prctl_set_seccomp`,
`prctl_get_seccomp`, `seccomp_get_action_avail`, `seccomp_get_notif_sizes`,
`bpf_prog_create_from_user`, `bpf_prepare_filter`, `bpf_migrate_filter`,
`bpf_check_basics_ok`, `bpf_check_classic`, `chk_code_allowed`,
`check_load_and_stores`, `bpf_convert_filter`, `bpf_prog_store_orig_filter`,
`bpf_release_orig_filter`, `__bpf_prog_release`, `bpf_prog_destroy`); and
the `cut_functions` the epoll design introduces, here `bpf_prog_realloc`,
`bpf_prog_select_runtime` and everything in `kernel/bpf/core.c`, which is
not listed. `kernel/sys.c` is not listed: `prctl`'s dispatch is below the
cut and the seccomp arms are witnessed in `kernel/seccomp.c`.

The existing suites are unaffected by listing `kernel/seccomp.c`: no
process in them sets a mode, `copy_seccomp` and `seccomp_filter_release`
return at their first test for a task without a filter, and both run
outside every window in those suites (the pin holder forks at batch
level; exits follow the result line).

## 7. Generator and corpus

`scripts/seccomp-corpus.py` writes `corpus/seccomp/` (hand-written, with
the program listings in the trace file so the review reads them) and
`corpus/seccomp-controls/`; `evaluator/generate.py` gains a `seccomp`
profile for the generated set.

Hand-written (about 40 traces), one per arm:

- install: the `RET ALLOW` singleton; the canonical prologue alone; the
  NULL program; length 0, 4097 and 4096; a bad pointer (`-EFAULT`); each
  flag-mask arm and each invalid flag combination; `prctl` with mode 0 and
  3;
- checker: one trace per `-EINVAL` arm of 2.5 (unknown code, `DIV|K` 0,
  `MOD|K` 0, `LSH|K` 32, `ST` 16, `JA` past the end, `jt` past the end,
  `jf` past the end, a last instruction that is not `RET`, an unknown
  ancillary offset, a known ancillary offset rejected by seccomp, a
  misaligned CTX load, a CTX load at 64, `LD|H|ABS`, `LDX|MSH`, `MOD|X`,
  a load of an unstored cell, a load of a cell stored on one path only);
  and the `LEN` rewrite with a program that returns `ALLOW` iff `LEN ==
  64`;
- actions: `ERRNO` with data 1, 4095, 4096, 65535; `TRAP` with data;
  `LOG`; `TRACE` (the `-ENOSYS` arm); `KILL_THREAD`, `KILL_PROCESS` and
  action `0x10000` in a child; `ALLOW` on 1000 (`-ENOSYS` from the table,
  cache miss witnessed);
- chains: two filters where the older kills and the newer allows (the
  cache's `bitmap_copy` arm, the most-restrictive rule); the reverse; two
  with equal actions and different data (the tie rule); a third filter;
  four 4096-instruction filters of two-instruction jumps to cross
  `MAX_INSNS_PER_PATH` (`-ENOMEM` at the fourth), which is also the one
  trace where `bpf_prog_realloc` takes its allocating arm;
- modes and privilege: strict in a child then an allowed call (`exit`),
  then a killed one (`SIGKILL`); strict after filter (`-EINVAL`); filter
  after strict in a child (the `seccomp` call itself is killed);
  `capdrop` then install (`-EACCES`), then `set_no_new_privs` then install
  (0); the `prctl` argument arms; `get_seccomp` before and after;
  `get_action_avail` for each action and one unknown; `get_notif_sizes`;
- the uretprobe exception: a filter killing 335, a child probe of 335,
  observed as `SIGILL` from the call itself, never `SIGSYS`;
- mixed: a filter, then eventfd and pipe ops, to witness the cache path
  on harness calls and the file table unchanged by seccomp.

Generated (about 300 traces, seeded): (g1) **checker fuzz**, 1-24 random
`sock_filter` words over the whole code space, install only, for the
checker's verdict; (g2) **behaviour**, 1-3 chained filters from the
prologue plus a random body over the seccomp language (loads of `nr`,
`arch`, `args[k]`; ALU with immediates and `X`; stores and loads of
cells after stores; forward jumps; `RET` with a random action, canonical
or not, and random data), then 2-6 probes over the probe set with random
arguments, `self` where the rule allows and `child` otherwise; (g3)
**mixed**, g2 interleaved with the pipe profile's ops.

Controls (`corpus/seccomp-controls/`): `tsync` and `new_listener` flags,
a `USER_NOTIF` action, a filter loading offset 8, each expected to stop
`unsupported` at the named site while the kernel runs it; and a harness
unit test that the validator rejects `self` after a killing filter and
`strict` in the trace process.

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
  `kernel/seccomp.c`; the kernel identity;
- speedbumps: the sentinel above; the control suite.

The claim point's commit message carries the counts and the user's
signoff; no bundle, no narrative.

## 9. Out of scope (fail-noisy), and why

### 9.1 Stops the validator and the mirror make

| What | Where it stops | Why |
| --- | --- | --- |
| `TSYNC`, `TSYNC_ESRCH` | validator; mirror `unsupported` at `seccomp_attach_filter` | thread iteration over a single thread is dead code made live only by a second thread |
| `NEW_LISTENER`, `WAIT_KILLABLE_RECV`, `USER_NOTIF` | validator; mirror `unsupported` at `seccomp_set_mode_filter` / `__seccomp_filter` | a listener file and a blocking protocol |
| `TRACE` with a tracer | mirror `unsupported` at the `ptrace_event_enabled` cut | no tracer in the fixture; the no-tracer arm is in scope |
| a CTX load of offsets 8..15 at run time | engine `unsupportedRead` | `instruction_pointer` is not recorded |
| strict mode in the trace process | validator | the process could not report (6.2) |
| a second thread | not expressible | single-task domain |

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
(`BPF_JIT` unset).

### 9.3 Modelled but unexercised, and said so

The `-ENOMEM` arms of allocation sites 4 and 5 (and 2 and 10 if step 0
finds them unrecorded); `-EFAULT` from the instruction copy with a
partially valid buffer; `bpf_convert_filter`'s `pass > 2` arm (the C's
comment says the second pass must converge); the `WARN_ON` fall-off in
`seccomp_is_const_allow` (impossible for a checked program: it ends in
`RET`). Each is a decision the mirror emits and no trace witnesses; the
check's `known_gaps` does not list them, since they are modelled.

## 10. Risks

1. **vmalloc allocation records** (3.1). If sites 2 and 10 are not
   resolvable, two `-ENOMEM` arms are unexercised; nothing else moves.
2. **The child probe's plumbing** (6.2): a second KCOV descriptor, a
   shared mapping, a shared result page, `RLIMIT_CORE`, `exit` versus
   `exit_group` under strict. About 80 lines of guest C with several ways
   to be subtly wrong; step 0 builds it first, on a scratch kernel. The
   fallback, if the shared mapping does not survive the child's death as
   2.8 and `kcov_mmap`'s `vm_insert_page` (`kernel/kcov.c:508`) suggest it
   does, is a child probe without coverage, declared as an unwitnessed op
   in `kcov.json`; the data check of the kill still holds.
3. **Decision volume.** `seccomp_cache_prepare` emulates the program 463
   times per install, each a handful of decisions: roughly ten thousand
   mirror decisions and a similar number of comparison records per
   install. Within KCOV's area, but the check's per-op intersection is
   Python; step 0 times a three-filter trace. If it is too slow, the
   emulation becomes a cut with its result (the bitmap) as data, at the
   cost of 4.6's statement 2 losing its control-flow witness.
4. **The engine subset.** `MiniInterp` must match the interpreter on the
   emitted opcodes (shift masking, 32-bit wrap, the negative-immediate
   temporary). g2's random ALU bodies are the test; a disagreement shows
   as a data mismatch on a probe with the translation's decisions all
   witnessed, which points at the engine.
5. **`TRAP`'s return value** is an x86 register fact (2.2); if the
   measurement shows anything but the call number, it is excluded as an
   operand rather than modelled.
6. **The `pages` decision** needs `offsetof(struct bpf_prog, insnsi)`
   (3.1); a wrong constant shows as the `pages <=` arm mismatching on the
   large-filter trace only.
7. **Config.** `CONFIG_SECCOMP=y` is additive (2.1, 6.3); the regression
   claim on the existing corpora is the evidence. It is the first
   behaviour-bearing config change since the 2026-10-07 rule; the user
   opened the case on 2026-10-12.

## 11. Execution plan

| Step | Stream | Work | WU |
| --- | --- | --- | --- |
| 0 | coordinator | A scratch build with `CONFIG_SECCOMP=y` (not the oracle; under `capped`); the child-probe plumbing prototyped in the guest against it; the kind-305 records of one install, site-resolved; the DWARF constant of 3.1; `TRAP`'s return value; the decision count and check time of a three-filter trace. | 0.05 |
| 1 | coordinator | The interface commit: opcodes 30-34 named, `AllocSite` and `HiddenSite` ids in 200-219, the `SeccompState` and `Task` fields, `cut_functions` and the files of 6.3, the `seccomp_child` fixture flag, `CONFIG_SECCOMP=y` in `kernel/config-x86_64-net-choice`, and the kind-309 record if approved (13.3). | 0.02 |
| 2 | U | `Classic.lean`, `Translate.lean`, `Engine.lean` with `MiniInterp` and `classicRun`; the Lean-side equality check of 8; unit tests on the hand-written rejection set. | 0.25 |
| 3 | V | `Filter.lean`, `Syscalls.lean`, the `Task` fields, the per-op `secureComputing` pre-step in dispatch, fork-inherit and release for the child probe, the observations. Depends on 1 and U's types (not U's bodies). | 0.3 |
| 4 | W | The five operations, both probe modes, the handler, descriptor 8, `RLIMIT_CORE`, `capset`; `trace.py` fields and the validator rules of 6.1; `linux.py`'s fixture row; the contract; `kcov.json`; the oracle rebuild shared with epoll and its identity. | 0.2 |
| 5 | X | `seccomp-corpus.py`, the generated profile, the controls, the sentinel, the claim point: full check on the new oracle, controls, sentinel, then one signoff. | 0.15 |

About 1.0 WU in all, above the scout's 0.5-0.7 band by the child probe
and the translation mirror, which the scout did not count. U and V run in
parallel after step 1 (V stubs the engine with `classicRun` until U
lands); W runs in parallel with both; X starts when V passes the
hand-written set on the scratch kernel and finishes on the oracle. The
oracle rebuild is the one shared with epoll's kind-308 record, after both
designs are audited (`docs/decisions.md`, 2026-10-12).

## 12. File ownership

| Stream | Files |
| --- | --- |
| U | `Leanux/Seccomp/Classic.lean`, `Translate.lean`, `Engine.lean`, `Consts.lean` (new); `tests/Seccomp*.lean` |
| V | `Leanux/Seccomp/Filter.lean`, `Syscalls.lean` (new); `Leanux/Runner.lean` (dispatch and observation); the `Task` fields after the interface commit |
| W | `harness/guest.c`, `harness/trace.py`, `harness/linux.py`, `contracts/trace-v1.md`, `correspondence/kcov.json`, `kernel/config-x86_64-net-choice`, `kernel/identity-*.txt`, `kernel/patches/gen-choice-stream.py` (only if 13.3 is approved) |
| X | `scripts/seccomp-corpus.py`, `corpus/seccomp/`, `corpus/seccomp-controls/`, `evaluator/generate.py`, the sentinel script |
| coordinator | `Leanux/Kernel/Defs.lean` (the interface commit), `docs/decisions.md` |

## 13. Decisions for the user

1. **`TRAP` in scope through a `SIGSYS` handler** (2.2, 6.2 rule 3).
   Recommended: it is the one action besides `ERRNO` that real sandboxes
   use for emulation, and the handler costs ten lines.
2. **The child probe with a second KCOV descriptor at 8** (6.2 rule 2)
   rather than unwitnessed child probes or a `CLONE_VM` child.
   Recommended: it is the only way to witness the kill arm, and the
   reserved descriptor follows the fixture's existing pattern.
3. **A kind-309 record of the translated program** (record-only: at the
   end of `bpf_migrate_filter`'s second pass, the eBPF length and up to
   256 instructions, before `bpf_prog_lock_ro`), compared by the mirror as
   data. Recommended: without it, the translation is checked only through
   the engine's behaviour and the path budget; with it, statement 4 of
   4.6 has a byte-level witness in every install. It is a record-only
   kernel change under the approved class, with per-merge signoff, and it
   rides the same rebuild.
4. **Strict mode in scope, child-only** (2.9). Recommended at about 0.03
   WU; it is the original seccomp and the `may_assign_mode` arms need it.
5. **`TRACE` without a tracer in scope** (2.2), a widening of the brief's
   exclusion list by one `if`. Recommended: it removes a stop from a
   generated action; the tracer arm stays out.
6. **The engine contract as a typeclass with `MiniInterp`** (4.4) rather
   than running the classic semantics directly on the modelled path.
   Recommended: it keeps the translation on the modelled path and gives
   the JIT project a drop-in point.
7. **The config case**: `CONFIG_SECCOMP=y`, with `SECCOMP_FILTER` following
   (`arch/Kconfig`: `def_bool y` under `HAVE_ARCH_SECCOMP_FILTER && SECCOMP
   && NET`), in one rebuild with epoll's record. Already opened by the
   user's decision of 2026-10-12; restated here with what it selects
   (2.1, 6.3) for the signoff at the rebuild.

Tactical choices made here under the user's standing delegation, to be
recorded in `docs/decisions.md` by the coordinator: the probe set and the
prologue rule (6.2 rule 1), the wire mapping and the sub-commands of ops
32 and 34 (6.1), the validator's syntactic kill rule (6.1), the sentinel
(7), the uretprobe control (7).

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
