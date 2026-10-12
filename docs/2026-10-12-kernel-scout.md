# Kernel scout: candidate mirror targets (2026-10-12)

Status: **read-only assessment [AGENT, Opus scout]**. It is not a plan, and
it changes no standing rule. Choosing a next target, and every config or
kernel change named below, is the user's decision.

Scope and evidence:
- Kernel facts are from the locked tree `.deps/linux` (6.12.110). Line counts
  come from `wc -l` on that tree, and function anchors from `grep -n`.
- The current oracle configuration is `kernel/config-x86_64-net-choice`, and
  the guest command line is in `harness/linux.py:739`.
- QEMU facts come from the bundled QEMU 8.2.2 (`scripts/in-bundle`), using
  only capability queries:
  - `-cpu help`;
  - `-machine virt,help` and `-help` for aarch64;
  - three QMP `query-cpu-model-expansion` calls on a `-machine none`
    process. That process has no CPUs and runs no guest code, so no guest
    was booted.
- I ran no builds, checks or guests.
- Prior-work citations are limited to sources I could confirm (section 7).
  "None found" means I found none, not that none exists.

## 1. The method, as a target must meet it

What a target must fit (AGENTS.md; way-forward section 3; the choice-stream
strategy; dispatch order; the simulation-target review):
- **The mirror is thin and executable.** It has one mirror structure per C
  struct on the path, one function per C function or lock region, and the
  C's choice points in the C's order. Out-of-scope arms are fail-noisy
  `unsupported` outcomes.
- **Hidden inputs are records.** These are random draws, clock reads,
  allocation outcomes, and which queued unit a dispatch runs. They are
  recorded at generic interception points in `kcov.c`, `random.c`,
  `timekeeping.c`, `workqueue.c`, `timer.c`, `softirq.c` and the slab/page
  fault hooks. The mirror consumes them in sequence order.
- **The check has three parts:**
  - observations (A1);
  - decision coverage against KCOV witnesses (A2);
  - declared operand comparisons (A3).

  It runs on a single-CPU, `PREEMPT_NONE`, Tiny-RCU x86_64 guest under QEMU
  TCG (`-cpu qemu64 -smp 1`).
- **Declared debt** (choice-stream section 7) is anything the instruments
  cannot see:
  - hardirq context, including every hrtimer, because `HIGH_RES_TIMERS` is
    unset and expiry runs from `hrtimer_run_queues` in the tick,
    `kernel/time/timer.c:2466`, `hrtimer.c:1944-1974`;
  - lockless interleavings;
  - SMP;
  - dispatches outside the armed set.
- **The simulation proof will want** (review section 1):
  - owned-once objects with identities;
  - explicit service contracts at cuts;
  - lifetime-scoped identities;
  - no arbitrary fuel;
  - suspended activations at yields.

  A target whose natural structure already has these properties is cheaper
  to prove later.

Two facts about this configuration shape every candidate:

1. **What the oracle has switched off.** Many attractive targets are
   compiled out:
   - `SECCOMP`, `SECURITY` (so Landlock), `BPF_SYSCALL`, `SYSVIPC`,
     `POSIX_MQUEUE`, `KEYS`, `INOTIFY_USER`, `USERFAULTFD`, `NETFILTER`,
     `PACKET`;
   - `VIRTUALIZATION` (so KVM).

   AGENTS.md classifies a config change as a behaviour change, and each one
   needs its own case put to the user. The table marks such candidates with
   **cfg**.
2. **Which code KCOV does not see.** The following are not instrumented:
   - `kernel/sched` (`KCOV_INSTRUMENT := n`, `kernel/sched/Makefile:9`),
     which covers the scheduler and `wait.c`;
   - `kernel/locking`;
   - `kernel/entry` (`kernel/entry/Makefile`);
   - `lib/rbtree.o` (`lib/Makefile:12`);
   - `softirq.o`.

   These are natural cut points. One consequence: wait-queue wakeup loops
   and rbtree rebalancing are below the cut wherever they appear.

**A gap shared by several candidates.** The hidden inputs cover deferred
units (work, timers, NET_RX), but not **which task the scheduler runs**
after a blocking call or wakeup. Kind 302 records only a `cond_resched`
inside a task section. Anything that blocks across two user tasks needs a
new, record-only "task switch" record at `__schedule`, or a scope
restricted to non-blocking calls:
- futex;
- blocking AF_UNIX, pty and mqueue I/O;
- seccomp user notification.

## 2. Criteria and scoring

Each criterion is scored 0 to 3, where 3 is the best fit:

| # | Criterion | 3 means |
|---|---|---|
| C1 | Reachable and deterministic on one CPU, given the records | No unrecorded nondeterminism in scope |
| C2 | Observable through a guest interface | Syscalls, ioctls or netlink give rich, comparable results |
| C3 | KCOV coverage | The code is compiled into vmlinux and instrumented, with no gaps on the path |
| C4 | Bounded, same-shaped state | Small C structs that map one to one |
| C5 | Control-flow richness and relevance | Many meaningful choice points; security or correctness history |
| C6 | Prior formal work to connect to | Directly on this Linux code |
| C7 | Effort to a complete single-CPU mirror | In WireGuard units (WU, below) |
| C8 | Hidden inputs | "covered" by the existing generic points, or the new point needed |
| C9 | Fit with the later separation-logic proof | Small anchored surface, clear service boundaries |

**The effort unit (WU).** One WU is WireGuard, which took about three weeks
of parallel agent streams:
- 6,066 C lines in `drivers/net/wireguard`;
- 4,898 Lean lines in `Leanux/WG`;
- the choice-stream, dispatch and allocation infrastructure, built over the
  same period.

The calibration point for a hook-free target on today's infrastructure is
pipes, which took about a week from design to the last follow-up
(2026-10-05 to 2026-10-11):
- `fs/pipe.c`, 1,522 lines;
- `Leanux/FS/Pipe.lean`, 634 lines;
- zero new hooks.

That gives roughly **0.2 WU per 1k C lines** of hook-free, FS-like code. I
add a premium for new instruments, a new architecture, or a config case.

## 3. Candidate table

The total is C1 to C6 plus C9, out of 21. It is a reading aid, not a
weighting.

| # | Candidate (6.12.110 sources) | C1 | C2 | C3 | C4 | C5 | C6 | C9 | Total | C7 effort | C8 hidden inputs | Config |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | **epoll** (`fs/eventpoll.c` 2,838) over the mirrored eventfd and pipe | 3 | 3 | 3 | 3 | 2 | 0 | 3 | **17** | 0.35–0.5 | covered: clock `eventpoll.c:2120` (timeout), allocation | on |
| 2 | **IPv4 FIB trie via rtnetlink** (`net/ipv4/fib_trie.c` 3,047, `fib_frontend.c` 1,678, `fib_semantics.c` 2,300) | 3 | 3 | 3 | 3 | 2 | 0 | 3 | **17** | 0.6–0.9 | covered: allocation; `call_rcu` frees are a cut | on |
| 3 | **AF_UNIX + SCM_RIGHTS garbage collector** (`net/unix/af_unix.c` 3,854, `garbage.c` 646) | 2 | 3 | 3 | 2 | 3 | 0 | 2 | **15** | 0.8–1.2 | covered: autobind `get_random_u32` (`af_unix.c:1230`), GC work on `system_unbound_wq` (`garbage.c:619`, a dispatch-set declaration), allocation. Blocking I/O needs the task-switch record | on (`UNIX`, `AF_UNIX_OOB`) |
| 4 | **seccomp filters + classic BPF check and interpreter** (`kernel/seccomp.c` 2,560; `net/core/filter.c` `bpf_check_classic` :1072, `bpf_convert_filter` :576; `kernel/bpf/core.c` `___bpf_prog_run` :1811) | 3 | 3 | 2 | 3 | 3 | 0 | 3 | **17** | 0.5–0.7 | covered (the notify id `get_random_u64`, `seccomp.c:1891`). User notification needs two tasks | **cfg**: `SECCOMP`, `SECCOMP_FILTER` |
| 5 | **x86 KVM control plane** (VM, memslot, irqchip, irqfd and ioeventfd ioctls; no `KVM_RUN`) (`virt/kvm/kvm_main.c` 6,575; `eventfd.c` 1,015; `irqchip.c` 263; `arch/x86/kvm/i8259.c` 660, `ioapic.c` 776, `irq_comm.c` 442) | 3 | 3 | 3 | 2 | 3 | 1 | 2 | **17** | 1.0–1.5 | covered: allocation; SRCU waits trivial with no vCPU running | **cfg**: `VIRTUALIZATION`, `KVM`, `KVM_AMD`. The oracle CPU already exposes SVM (section 6.2) |
| 6 | **signalfd + signal delivery** (`fs/signalfd.c` 359; `kernel/signal.c` 4,918, partly mirrored in `Leanux/Kernel/Signal.lean`) | 3 | 3 | 3 | 3 | 2 | 0 | 3 | 17 | 0.3–0.5 | covered | on |
| 7 | **memfd + file seals** (`mm/memfd.c` 495; `mm/shmem.c` below the cut) | 3 | 3 | 3 | 3 | 1 | 0 | 3 | 16 | 0.15–0.25 | covered (allocation, inode clock) | on |
| 8 | **generic netlink + `af_netlink` core** (`net/netlink/af_netlink.c` 2,958, `genetlink.c` 1,997) | 3 | 3 | 3 | 2 | 2 | 0 | 2 | 15 | 0.6–0.8 | covered | on |
| 9 | **POSIX mqueue** (`ipc/mqueue.c` 1,750) | 2 | 3 | 3 | 3 | 2 | 0 | 3 | 16 | 0.4–0.5 | non-blocking scope covered; blocking needs the task-switch record; timeouts are hrtimers (debt) | **cfg**: `POSIX_MQUEUE` |
| 10 | **Landlock** (`security/landlock/` 4,745 lines, of which `fs.c` 1,819, `ruleset.c` 738, `syscalls.c` 536) | 3 | 3 | 3 | 2 | 3 | 0 | 2 | 16 | 0.7–1.0 (needs a dentry-walk model) | covered (ruleset free via `schedule_work`, `ruleset.c:523`) | **cfg**: `SECURITY`, `SECURITY_LANDLOCK`, `lsm=` boot parameter |
| 11 | **pty + `n_tty` line discipline** (`drivers/tty/n_tty.c` 2,561, `pty.c` 947, `tty_buffer.c` 628) | 2 | 3 | 3 | 2 | 2 | 0 | 2 | 14 | 0.7–0.9 | covered: `flush_to_ldisc` on `system_unbound_wq` (a dispatch declaration). `jiffies` in `overrun_time` (`n_tty.c:1170`) is a declared gap | on (`UNIX98_PTYS`) |
| 12 | **futex** (non-PI, then PI and requeue) (`kernel/futex/` 4,658 across `core.c`, `waitwake.c`, `requeue.c`, `pi.c`, `syscalls.c`) | 1 | 2 | 3 | 2 | 3 | 0 | 2 | 13 | 0.8–1.2 | **new**: task-switch record. Timeouts are hrtimers (debt). The hash is `jhash2` of the key (`core.c:119`), so deterministic under `nokaslr` | on |
| 13 | **VMA management** (`mm/vma.c` 2,101, `mmap.c` 2,405, `mprotect.c` 915, `mremap.c` 1,223; `lib/maple_tree.c` 7,707 as a cut) | 2 | 2 | 3 | 1 | 3 | 0 | 2 | 13 | 1.5–2.0 | covered (mmap-base random draw; allocation); maple-tree preallocation needs care | on |
| 14 | **timerfd / POSIX timers / itimers** (`fs/timerfd.c` 628, `kernel/time/posix-timers.c` 1,564, `itimer.c` 403) | 1 | 3 | 2 | 3 | 2 | 0 | 2 | 13 | 0.5 + an instrument | **new**: hardirq hrtimer sections (expiry at `timerfd_tmrproc`, `timerfd.c:74`, runs in the tick's hardirq) | on |
| 15 | **x86 KVM vCPU run + MMU** (`arch/x86/kvm/x86.c` 14,181, `mmu/mmu.c` 7,824, `svm/svm.c` 5,665, `svm/nested.c` 1,842, `lapic.c` 3,433) | 1 | 2 | 2 | 1 | 3 | 1 | 1 | 11 | 3–4 | **new**: VMCB exit records (exit code, info, guest state after `VMRUN`), `rdtsc` reads, hrtimer (LAPIC timer) | **cfg** as row 5 |
| 16 | **arm64 host KVM (VHE)** incl. `kvm_pgtable` stage-2 (`arch/arm64/kvm/*.c` 24,069; `hyp/pgtable.c` 1,619) | 1 | 2 | 2 | 2 | 3 | 2 | 2 | 14 | 3–4 incl. an arm64 oracle | **new**: the whole arm64 pipeline (section 6.1) | new arch |
| 17 | **pKVM hypervisor** (nVHE/hVHE EL2) (`arch/arm64/kvm/hyp/nvhe/*.c` 6,910 lines, of which `mem_protect.c` 1,311, `pkvm.c` 618, `page_alloc.c` 248, `hyp-main.c` 511; shared `hyp/pgtable.c` 1,619) | 1 | 1 | 0 | 2 | 3 | 3 | 3 | 13 | 4–6 incl. infrastructure | **new**: the hyp-side coverage instrument, hypercall records, a hyp-state readout (section 6.1) | new arch, `kvm-arm.mode=protected` |
| 18 | **BPF verifier** (`kernel/bpf/verifier.c` 23,059, plus `syscall.c` 6,069, `tnum.c` 221, `btf.c`) | 3 | 3 | 3 | 1 | 3 | 3 | 1 | 17 | 4–6 | covered | **cfg**: `BPF_SYSCALL` |
| 19 | **io_uring** (`io_uring/*.c` 19,209 lines; `io_uring.c` 3,871, `io-wq.c` 1,421, `poll.c` 1,066) | 1 | 3 | 3 | 1 | 3 | 0 | 1 | 12 | 3+ | **new**: io-wq worker kthreads are not workqueue dispatches; `task_work` | on |
| 20 | **TCP** (`net/ipv4/tcp*.c` 35,780 lines, of which `tcp_input.c` 7,415, `tcp_output.c` 4,450, `tcp.c` 5,183) | 2 | 3 | 3 | 1 | 3 | 2 | 1 | 15 | 6+ | covered (timers are `timer_list`, ISN secret, clocks), except pacing and TSQ hrtimers (debt) | on |

Notes on the scores:
- **C6.** C6 is 0 wherever I found no formal work on that Linux code (section
  7).
- **pKVM C9.** pKVM's 3 is for its surface: about 1.3k lines of ownership
  logic behind about 25 hypercalls (`hyp-main.c:407-432`).
- **BPF verifier and TCP C9.** They score 1 for size and churn.
- **Total versus effort.** The total ignores effort. Rows 1, 2, 4, 5 and 18
  tie at 17, and effort separates them.

## 4. Profiles of the top candidates

### 4.1 epoll

**Scope.** Mainly `fs/eventpoll.c` (2,838 lines):
- `do_epoll_create` :2398;
- `do_epoll_ctl` :2479-2625, with `ep_insert` :1827, `ep_modify` :1910 and
  `ep_remove`;
- `ep_ptable_queue_proc` :1540 and `ep_poll_callback` :1429;
- `ep_send_events` :2058 and `ep_poll` :2161-2283;
- the nesting checks `ep_loop_check` :2364, `ep_loop_check_proc` :2296 and
  `reverse_path_check` :1655;
- `eventpoll_release_file` :1287 and `ep_free` :981.

**State.** The state is C-shaped:
- `eventpoll {rbr, rdllist, ovflist, wq, poll_wait}`;
- `epitem {ffd, rdllink, next, pwqlist, event, ws}`;
- `eppoll_entry` per wait-queue registration.

The rbtree is `lib/rbtree.o`, which KCOV does not instrument, so an
ordered-map cut is honest.

**Paths and hidden inputs.** It reuses the mirrored file table, eventfd and
pipe, and their `f_op->poll`. Readiness callbacks run synchronously in the
waker's task: a `write` to a watched eventfd calls `ep_poll_callback` inside
that syscall. A trace of `epoll_ctl`, `write`, `epoll_wait(timeout 0)` and
`close` is therefore one task with no new hidden input. A non-zero timeout
reads `ktime_get_ts64` (:2120), which is already hooked.

**What it adds.**
- It forces the wait-queue entry and callback discipline that the pipes
  reconnaissance deferred (`docs/2026-10-05-pipes-reconnaissance.md:50-66`).
  That is a real service contract the later proof needs.
- The control flow has substance:
  - the edge- and level-triggered re-queue in `ep_send_events`;
  - `EPOLLONESHOT` and `EPOLLEXCLUSIVE`;
  - the `ovflist` path;
  - nested epoll with loop and reverse-path limits, the code behind past
    epoll CVEs.

**Estimate.** About 0.35 to 0.5 WU, with no kernel change.

### 4.2 IPv4 FIB trie via rtnetlink

**Scope.**
- In `net/ipv4/fib_trie.c` (3,047 lines):
  - `fib_table_insert` :1200, `fib_insert_node` :1110 and
    `fib_insert_alias` :1160;
  - `fib_table_delete` :1694;
  - `fib_table_lookup` :1426;
  - `resize` :848 with `inflate` :537, `halve` :633 and the thresholds
    :290-293;
  - `fib_table_dump` :2335.
- The `fib_info` sharing in `fib_semantics.c`.
- The rtnetlink entry points in `fib_frontend.c`.

**State.** `key_vector` nodes with power-of-two child arrays map one to one
to keyed identities. This is an LC-trie, close in kind to the allowed-IPs
trie already mirrored (`Leanux/WG/AllowedIps.lean`), so the representation
experience transfers.

**Interface and hidden inputs.** Driven by `RTM_NEWROUTE`, `RTM_DELROUTE`,
`RTM_GETROUTE` (a single lookup, fully observable) and dumps. Hidden inputs
are allocation outcomes only, and node frees are `call_rcu` cuts. With
`IP_ADVANCED_ROUTER` unset there is a single table.

**What it adds.**
- **Payoff for WireGuard.** Routing is summarized in the environment
  (`World.route4/route6/routeLookup`, `Leanux/Kernel/Defs.lean:1149-1197`,
  per the review section 3.3). A mirrored FIB turns that summary into
  mirrored code with a contract boundary. That is exactly the "explicit
  service implementation" the review asks for.
- **Rich decisions.** The resize heuristics and lookup backtracking supply
  them. The relevance is correctness rather than security.

**Estimate.** 0.6 to 0.9 WU, with no kernel change.

### 4.3 AF_UNIX sockets and the SCM_RIGHTS garbage collector

**Scope.**
- `net/unix/af_unix.c` (3,854 lines): stream, datagram and seqpacket
  send/recv, peek offsets, `MSG_OOB` (on in this config), autobind,
  socketpair.
- `net/unix/garbage.c` (646 lines), the 6.10+ graph collector:
  - edges: `unix_add_edges` :192, `unix_del_edges` :227;
  - Tarjan SCC walk: `__unix_walk_scc` :444, `unix_walk_scc` :536,
    `unix_walk_scc_fast` :559;
  - `unix_scc_dead` :364;
  - `__unix_gc` :581 and `wait_for_unix_gc` :625.

**Why it matters.** In-flight file-descriptor GC has a long history of
exploitable bugs; the GC race CVE-2021-0920 was exploited in the wild.

**State.** The state is bounded and C-shaped:
- `unix_sock`;
- `unix_vertex {edges, out_degree, index, scc_index}`;
- `unix_edge`;
- `scm_fp_list`;
- the receive queues.

**Hidden inputs.**
- The GC runs as `unix_gc_work` on `system_unbound_wq` (:619). That is an
  ordinary armed-dispatch declaration with no new hook.
- Autobind's starting `ordernum` is a `get_random_u32` draw (:1230), which
  is already hooked.
- Blocking `recv` and `send` across two tasks needs the task-switch record.
  A first stage can use `MSG_DONTWAIT` and single-task `socketpair` traces,
  which cover the GC fully: close cycles, then trigger GC.

**The cost driver.** skbs carrying files must be owned-once identities. The
review's section 4.2 says WireGuard should have done this; here it is
unavoidable, which makes this target a good place to establish the
discipline.

**Estimate.** 0.8 to 1.2 WU.

### 4.4 seccomp

**Scope.** `kernel/seccomp.c` (2,560 lines):
- `seccomp_set_mode_filter` :1947;
- `seccomp_prepare_filter` :661 and `seccomp_check_filter` :280;
- `seccomp_attach_filter` :913;
- the action cache: `seccomp_cache_prepare` :881 and `seccomp_is_const_allow`
  :762-838, a small abstract evaluator of cBPF over the architecture and
  syscall number;
- `seccomp_run_filters` :406;
- `__seccomp_filter` :1244 and `__secure_computing` :1378;
- the user notifier :1442-1916.

Below these, in `net/core/filter.c`: `bpf_check_classic` :1072,
`check_load_and_stores` :928 and `bpf_convert_filter` :576. The program then
runs on the instrumented interpreter `___bpf_prog_run`
(`kernel/bpf/core.c:1811`), since `BPF_JIT` is unset.

**State.** Small: a refcounted filter chain with a cache bitmap per filter.

**Observations.**
- `seccomp(2)` and `prctl` results;
- the errno, `SIGSYS` or `SECCOMP_RET_TRAP` outcome of every later syscall;
- `SECCOMP_GET_ACTION_AVAIL`.

**Caveats.**
- The caller in `kernel/entry` is not instrumented, though `seccomp.c` is.
  This is harmless, because the decisions live in `seccomp.c`.
- A filter applies to the trace process's own KCOV readout syscalls, so the
  guest runner must install it after setup and allow those syscalls. That is
  a harness change.
- It needs a config case.

**Estimate.** 0.5 to 0.7 WU, including a mirrored cBPF interpreter. Mirrored
as interpreter cases, the interpreter is a clean, finite instruction set.

### 4.5 x86 KVM control plane

**Scope.**
- `virt/kvm/kvm_main.c`:
  - `kvm_create_vm` :1146;
  - the memslot machinery:
    - `check_memory_region_flags` :1574;
    - `kvm_replace_memslot` :1513;
    - `kvm_swap_active_memslots` :1601;
    - `kvm_prepare_memory_region` :1659 and `kvm_commit_memory_region`
      :1697;
    - `kvm_set_memslot` :1872;
    - `__kvm_set_memory_region` :1988-2109;
    - about 600 lines in all;
  - `kvm_vm_ioctl_create_vcpu` :4218;
  - the ioctl dispatchers `kvm_dev_ioctl` :5536, `kvm_vm_ioctl` :5161 and
    `kvm_vcpu_ioctl` :4446.
- `kvm_set_irq_routing` (`irqchip.c:168`).
- irqfd and ioeventfd: `kvm_irqfd_assign` (`eventfd.c:319`) and
  `kvm_assign_ioeventfd_idx` :826. They sit on the already-mirrored eventfd.
- The in-kernel PIC and IOAPIC (`i8259.c`, `ioapic.c`), with state readable
  through `KVM_GET_IRQCHIP`.

**State.** Memslots are two generations of `kvm_memslots`, each with a gfn
rbtree, an hva interval tree and an id hash. That state is same-shaped but
needs care.

**Determinism.** With no vCPU running, the SRCU synchronizations in
`kvm_swap_active_memslots` have no readers.

**Relevance.** This is the host attack surface that a VMM drives, with prior
art (section 7).

**Requirements.**
- A config case (`VIRTUALIZATION`, `KVM`, `KVM_AMD`).
- KVM initialization stays within the 256 MB guest.

**Estimate.** 1.0 to 1.5 WU.

## 5. Briefer notes on the rest

- **signalfd and signals.** The cheapest extension of existing work, since
  `Leanux/Kernel/Signal.lean` already mirrors the pending set. It is small
  but useful as glue for pty, mqueue and seccomp's `SIGSYS`.
- **memfd seals.** Tiny. It is a good warm-up or a filler stream, but has
  few choice points.
- **Netlink core.** It would retire cuts under WireGuard's netlink
  configuration path. It pays mostly as infrastructure.
- **POSIX mqueue.** Self-contained (a priority rbtree of `posix_msg_tree_node`)
  and needs a config case. Its value is mostly a cheap IPC object.
- **Landlock.** High security value. The obstacle is that
  `is_access_to_paths_allowed` walks dentries upward, so the mirror needs a
  dentry-tree service with a contract. That service is not built, and VFS
  path walk itself is lockless RCU-walk code. It is best after a VFS
  namespace model exists.
- **pty and n_tty.** Good dispatch-driven control flow
  (`flush_to_ldisc` work). The historical n_tty CVEs are SMP races, outside
  the domain.
- **futex.** The richest security history of the small targets. It is
  blocked on the task-switch record, and PI pulls in `rt_mutex`
  (`kernel/locking`, not instrumented, so it must be a cut).
- **VMA management.** High relevance. The maple tree (7,707 lines,
  instrumented) would have to be a declared cut with an interval-map
  contract, and every covered maple-tree function would need listing.
  Large.
- **timerfd and POSIX timers.** Not viable until hardirq sections exist,
  because expiry runs in the tick's hardirq.
- **io_uring.** The io-wq workers are kthreads outside the armed-dispatch
  mechanism, and completions run through `task_work`. It needs new dispatch
  instruments and is large.
- **TCP.** NetSem (section 7) shows the value of a TCP test oracle, but a
  C-shaped mirror is many WU. It would also inherit every packet-identity
  issue the review raised.

## 6. KVM and pKVM in depth

### 6.1 pKVM (arm64, nVHE/hVHE at EL2)

**What pKVM is in 6.12.**
- `kvm-arm.mode=protected` (`arch/arm64/kvm/arm.c:2858-2894`) aliases to
  `arm64_sw.hvhe=1` (`arch/arm64/kernel/pi/idreg-override.c:223`). The hyp
  then runs as a separate EL2 image, and the host kernel is deprivileged to
  EL1 under a host stage-2.
- The hyp handles about 25 host hypercalls (`hyp-main.c:407-432`). Ownership
  logic lives in `mem_protect.c` (1,311 lines):
  - the share, unshare and donate state machines `check_share`, `__do_share`,
    `check_unshare` and `check_donation` (:830-1090);
  - `__pkvm_host_share_hyp` :1092, `__pkvm_host_unshare_hyp` :1125,
    `__pkvm_host_donate_hyp` :1158 and `__pkvm_hyp_donate_host` :1190;
  - `host_stage2_idmap` :508 for lazily mapped host memory.
- Page ownership lives in software bits of the host stage-2 entries.
- VM shadow state is set up by `__pkvm_init_vm`, `__pkvm_init_vcpu` and
  `__pkvm_teardown_vm` (`hyp/nvhe/pkvm.c:446-618`).
- Memory comes from the buddy allocator (`hyp/nvhe/page_alloc.c`, 248 lines;
  `hyp_alloc_pages` :198, `__hyp_attach_page` :93).
- **No protected guests in 6.12.110.** `mem_protect.c` has host↔hyp and
  host↔FF-A transitions only, and no host-to-guest donation. The UAPI has no
  Arm protected-VM type (`include/uapi/linux/kvm.h` has only s390 protected
  capabilities). Upstream pKVM at this version protects the hypervisor from
  the host, and runs ordinary VMs whose state the hyp shadows.

**What the method would need, item by item.**

1. **An arm64 oracle.** It needs:
   - a new kernel profile and identity file;
   - an aarch64 guest initramfs;
   - the runner, guest agent and coverage symbolization ported off x86.
     `evaluator/coverage.py` is x86-specific, for example its tail-jump
     check.

   The bundle has `qemu-system-aarch64` 8.2.2, whose `virt` machine
   accepts `virtualization=on` and `gic-version` (confirmed by
   `-machine virt,help`). Syzkaller runs arm64 KVM fuzzing on exactly
   `-machine virt,virtualization=on,gic-version=max -cpu max` under QEMU
   (`.deps/syzkaller/vm/qemu/qemu.go:161`). EL2 under TCG is therefore an
   established configuration, though I did not boot it.

   arm64 is always SMP (`arch/arm64/Kconfig:373-374`, `config SMP def_bool
   y`). One CPU therefore means `-smp 1` with `SMP=y`: Tree RCU, real
   per-CPU machinery and IPI paths compiled in. That is a different oracle
   from the x86 Tiny-RCU one, and the environment-model assumptions would
   need revalidation.
2. **KCOV for hyp code: there is none.**
   - The nVHE objects are built as `%.nvhe.o` targets and linked into one
     `kvm_nvhe.o` (`hyp/nvhe/Makefile`, `hyp-obj-y`, `obj-y :=
     kvm_nvhe.o`). They are therefore not "kernel objects" in the sense of
     `scripts/Makefile.lib:204-207`, so `KCOV_INSTRUMENT_ALL` does not apply
     (`Makefile.lib:175`).
   - KCOV's runtime could not run at EL2 anyway: it reads `current` and EL1
     per-CPU state.
   - **The decision-coverage gate needs a different witness.** The options
     are:
     - **(a)** a QEMU TCG plugin recording EL2 PCs. The binary accepts
       `-plugin`, but the bundle ships no plugin, and one would have to be
       built against QEMU 8.2's `qemu-plugin.h`, which is not in the bundle.
     - **(b)** a hyp-local `__sanitizer_cov_trace_pc` writing to a
       hyp-owned buffer, read out by a debug hypercall. Sharing that buffer
       with the host is itself a page-ownership transition, so it perturbs
       the very state being checked. It must be donated at init and
       excluded from the comparison.
     - **(c)** a ghost-state instrumentation in the style of the SOSP 2025
       work (section 7).

     Each is a new trust-surface instrument and needs its own mutant
     evidence under "checks must pay for themselves".
3. **Observing the interface.**
   - **Host side.** Every hypercall goes through the `kvm_call_hyp_nvhe`
     macro (`arch/arm64/include/asm/kvm_host.h:1129`). That is one inline
     chokepoint in instrumented host code, where a record-only hook could
     log `(function id, arguments, return)` as a new record kind. From the
     host-mirror side the return values are hidden inputs, like device
     bytes.
   - **Hyp state.** Its page tables, ownership bits and allocator free
     lists are by design unreadable from the host. A readout needs an
     EL2-side dump: a debug hypercall writing the host stage-2 ownership
     map and the `hyp_pool` lists into a pre-donated buffer. The guest-side
     observations would be hypercall results, host stage-2 faults (a host
     touching a hyp-owned page takes an injected abort), and `KVM_RUN`
     outcomes.
   - **No userspace path to the interesting arms.** The interesting
     `check_share` and `check_donation` arms are reached from host kernel
     paths, such as vCPU and VM creation sharing structures with the hyp,
     not directly from userspace. The harness would drive them through KVM
     ioctls and could not choose arbitrary arguments.
   - **Implication.** Driving the hyp's error arms deliberately (double
     share, unshare of a non-shared page) needs either a test hypercall
     path or host-kernel fault injection. Both are behaviour changes.
4. **Hidden inputs at EL2.** The hyp reads no random or clock sources on
   these paths; its inputs are host-supplied arguments and the host's
   memory layout. Once the hypercall stream is recorded, the hyp is
   deterministic on one CPU, which is favourable. The difficulty is
   entirely in observation and coverage, not determinism.
5. **The host side of arm64 KVM as a target in its own right.** Yes, and it
   is the more method-compatible route:
   - The shared page-table walker `hyp/pgtable.c` (1,619 lines) is compiled
     twice:
     - into vmlinux as an ordinary, instrumented object
       (`arch/arm64/kvm/hyp/Makefile:10`, `obj-$(CONFIG_KVM) += ... pgtable.o`);
     - into the hyp image, uninstrumented (`hyp/nvhe/Makefile`,
       `../pgtable.o` in `hyp-obj-y`).
   - In default (VHE) or non-protected nVHE mode, the host manages guest
     stage-2 with that same source: `kvm_pgtable_stage2_init` and
     `kvm_pgtable_stage2_map` called from `arch/arm64/kvm/mmu.c:945,
     1133, 1688`.
   - The VHE hyp objects are ordinary `obj-y` objects
     (`hyp/vhe/Makefile`), so instrumented except for `noinstr` regions.
   - **The route.** An arm64 VHE oracle can mirror the very page-table code
     pKVM runs at EL2, with full KCOV witnesses, driven by
     `KVM_SET_USER_MEMORY_REGION` and guest stage-2 faults. It still needs
     the arm64 pipeline (item 1) and guest execution under TCG (exits as
     records, as for x86 in section 6.2).
   - **Later reuse.** A later pKVM step would then reuse the `kvm_pgtable`
     mirror and add only the ownership layer (`mem_protect.c`) and
     allocator (`page_alloc.c`) behind a hyp-coverage instrument.

**Prior verification relevant to pKVM** (section 7 for references):
- **CN (POPL 2023).** Verified pKVM's buddy allocator, the hyp page
  allocator (`page_alloc.c` in this tree), largely as written. Fulminate
  (POPL 2025) reports that case study as 320 lines of C with 702 lines of
  CN specification.
- **Islaris (PLDI 2022).** Verified machine code from pKVM that installs and
  calls exception vectors, against the authoritative Armv8-A ISA semantics.
- **Memarian et al. (SOSP 2025, "Ghost in the Android Shell").** An
  executable, test-oracle specification of pKVM's exception handlers and
  hypercalls. Abstraction functions map the concrete hyp state, including
  page tables, to C ghost state, with page tables interpreted as finite
  maps, and the spec is checked at runtime.

  This is the closest existing analogue of this project's method, applied
  to pKVM. Its abstraction functions and ghost state are what this project
  would otherwise have to invent for a hyp-state readout.
- **Not found.** I found no citable CN verification of pKVM's page-table
  code (`pgtable.c`) or of `mem_protect.c`. I do not claim one.
- **SeKVM (S&P 2021) and its USENIX Security 2021 follow-up.** Verified a
  retrofitted arm64 KVM core (KCore) in Coq. Not upstream pKVM, but the
  same architecture and split.

**Conclusion on pKVM** [AGENT]: pKVM is the **best-connected** target to
prior formal work (C6 = 3) and has a small, well-bounded surface (C9).
It is **not a good next target for this method**, for three reasons:
- it scores 0 on C3: no KCOV on the code that matters;
- it needs a second architecture with an SMP kernel and Tree RCU;
- its state is unobservable from the guest interface by design.

Each of these is a new instrument on the trust surface. Combined, they
make it 4 to 6 WU, most of it infrastructure.

**The credible path** is staged:
1. the x86 KVM control plane (section 6.2), to establish KVM-shaped state
   on the existing oracle;
2. an arm64 VHE oracle mirroring `hyp/pgtable.c` stage-2 code from the
   instrumented host copy;
3. only then, pKVM's `mem_protect.c` and `page_alloc.c`, with a
   hyp-coverage instrument. Option (a), the TCG plugin, does not perturb
   hyp memory and is the one I would put to the user. The hyp-state
   readout would be modelled on the SOSP 2025 ghost-state approach.

The last stage connects directly to CN's buddy-allocator specification and
the Cambridge executable spec.

### 6.2 x86 KVM inside the project's TCG guest

**Capability query results** (bundled QEMU 8.2.2, TCG):
- `-cpu help` lists both `svm*` and `vmx*` flag names. That shows QEMU
  recognizes them, not that TCG implements them.
- `query-cpu-model-expansion` under `-accel tcg` gave:
  - for `max`: `vendor AuthenticAMD`, `svm: true`, `npt: true`,
    `vgif: true`, `svme-addr-chk: true`, `nrip-save: false`, `vmx: false`,
    `vmx-ept: false`;
  - for **`qemu64`, the CPU the oracle already boots with**
    (`harness/linux.py:739`): `vendor AuthenticAMD`, `svm: true`,
    `npt: false`, `vmx: false`.
- So TCG emulates AMD SVM, with nested paging on `max`. It does not offer
  Intel VMX.

**What KVM needs from the CPU.**
- `kvm_amd` requires an AMD or Hygon vendor and the SVM CPUID bit
  (`arch/x86/kvm/svm/svm.c:526-548`), plus generic FPU checks
  (`arch/x86/kvm/x86.c:9744-9768`).
- Missing NRIPS is tolerated, with fallbacks at `svm.c:386,435,454`.
- With `qemu64`, `npt: false` means KVM uses shadow paging (`npt_enabled`
  false, `svm.c:201`).
- With `-cpu max` (a harness change) it would use NPT and the TDP MMU.

**KCOV.** `arch/x86/kvm` and `virt/kvm` set no `KCOV_INSTRUMENT := n`, so
KVM is instrumented. The exceptions are the `vmenter.S` assembly and
`noinstr` sections.

**Implications.**
- **The control plane is in reach today** (row 5). It needs:
  - the config case `CONFIG_VIRTUALIZATION=y`, `KVM=y`, `KVM_AMD=y`;
  - no CPU-model change.

  That covers VM creation, memslots, IRQ routing, the in-kernel PIC and
  IOAPIC, irqfd and ioeventfd, all through ioctls on one CPU, with no
  vCPU execution. A boot probe is the first step: confirm that `kvm_amd`
  initializes on `qemu64` under TCG. That is a source-level expectation,
  not observed here.
- **`KVM_RUN` executes the L2 guest inside QEMU's TCG SVM emulation.**
  - **Synchronous exits are determined by guest code:** port I/O, MMIO,
    HLT, nested page faults.
  - **Asynchronous exits are not:** an L1 timer interrupt arriving during
    `VMRUN` depends on host time.
  - **Needed:** a new record-only hook after the `VMRUN` return in
    `svm_vcpu_run`, recording the VMCB exit code, exit info and the guest
    state the mirror would otherwise have to emulate. Also a hook on
    `rdtsc` reads, which the clock hooks do not cover. The LAPIC timer is
    an hrtimer, which is hardirq debt.
  - **Alternative.** QEMU `-icount` with `sleep=off` would make TCG
    deterministic. That is a harness behaviour change, and slower.
  - This is row 15: 3 to 4 WU, and it reaches the MMU, the most
    security-relevant part of x86 KVM.
- **No VMX means `arch/x86/kvm/vmx` (`vmx.c` 8,693, `nested.c` 7,343) is
  unreachable under TCG.** Only the SVM backend can be an oracle.

## 7. Prior formal work cited

- C. Pulte, D. C. Makwana, T. Sewell, K. Memarian, P. Sewell,
  N. Krishnaswami. *CN: Verifying Systems C Code with Separation-Logic
  Refinement Types.* POPL 2023, PACMPL 7(POPL):1. doi:10.1145/3571194.
  Case study: pKVM's buddy allocator.
  <https://www.cl.cam.ac.uk/~cp526/popl23.html>
- *Fulminate: Testing CN Separation-Logic Specifications in C.* POPL 2025,
  doi:10.1145/3704879. Reports the pKVM buddy allocator at 320 lines of C
  and 702 lines of specification.
  <https://www.cl.cam.ac.uk/~pes20/cn-testing-popl2025.pdf>
- M. Sammler, A. Hammond, R. Lepigre, B. Campbell, J. Pichon-Pharabod,
  D. Dreyer, D. Garg, P. Sewell. *Islaris: Verification of Machine Code
  Against Authoritative ISA Semantics.* PLDI 2022,
  doi:10.1145/3519939.3523434. Includes pKVM exception-vector code.
- K. Memarian, B. Simner, D. Kaloper-Meršinjak, T. Pérami, P. Sewell.
  *Ghost in the Android Shell: Pragmatic Test-oracle Specification of a
  Production Hypervisor.* SOSP 2025, doi:10.1145/3731569.3764817.
  <https://www.cl.cam.ac.uk/~pes20/Stuff/exec-spec-paper.pdf>. I could not
  fetch the PDF from this sandbox. The statements above are from its
  abstract and listing, not from its evaluation section.
- S.-W. Li, X. Li, R. Gu, J. Nieh, J. Z. Hui. *A Secure and Formally
  Verified Linux KVM Hypervisor.* IEEE S&P 2021,
  doi:10.1109/SP40001.2021.00049. Also *Formally Verified Memory Protection
  for a Commodity Multiprocessor Hypervisor*, USENIX Security 2021.
- H. Vishwanathan, M. Shachnai, S. Narayana, S. Nagarakatte. *Verifying the
  Verifier: eBPF Range Analysis Verification* (Agni). CAV 2023,
  doi:10.1007/978-3-031-37709-9_12. Also *Validating the eBPF verifier via
  state embedding* (OSDI 2024), which I found listed but did not read.
- L. Nelson, J. Van Geffen, E. Torlak, X. Wang. *Specification and
  verification in the field: Applying formal methods to BPF just-in-time
  compilers in the Linux kernel* (Jitterbug). OSDI 2020.
- T. Ridge, D. Sheets, T. Tuerk, A. Giugliano, A. Madhavapeddy, P. Sewell.
  *SibylFS: formal specification and oracle-based testing for POSIX and
  real-world file systems.* SOSP 2015, doi:10.1145/2815400.2815411. This is
  the test-oracle precedent for any VFS-level target (Landlock's path walk,
  memfd).
- S. Bishop et al. *Engineering with Logic: Rigorous Test-Oracle
  Specification and Validation for TCP/IP and the Sockets API.* JACM 66(1),
  2018, doi:10.1145/3243650 (NetSem). The precedent for sockets and TCP.

**Gaps.** I found no formal work to cite on Linux's implementations of:
- epoll;
- the FIB trie;
- AF_UNIX garbage collection;
- seccomp;
- Landlock;
- n_tty;
- futex;
- mqueue;
- VMA merging.

## 8. Recommendation [AGENT]

**Next target 1: epoll.** It is the cheapest high-scoring target
(0.35–0.5 WU), with no kernel or config change and no new instrument. It
composes directly with the mirrored file table, eventfd and pipes. It also
forces the one service contract the existing mirror lacks: wait-queue
registration and callbacks, `f_op->poll`. That contract is needed by every
later blocking-I/O target and by the simulation proof's service boundary.

**Next target 2: the IPv4 FIB trie via rtnetlink.** It is a bounded, owned,
identity-keyed data structure of exactly the kind the proof handles best,
and it needs no kernel or config change. It also **pays back into
WireGuard**: it replaces the environment's routing summary
(`World.route4/route6`) with mirrored code behind a real contract boundary,
one of the review's named repairs.

**Close alternates.**
- **AF_UNIX with the GC.** Higher security value, at 1 WU, and it forces
  skb identity, which the review wants anyway. Take it third, or second if
  security relevance outweighs WireGuard payback.
- **The x86 KVM control plane.** The right first step towards
  KVM and pKVM, but it needs a config case. Put that case to the user now
  if virtualization is a strategic direction.

**The target to avoid: the eBPF verifier** (`kernel/bpf/verifier.c`,
23,059 lines). It is tempting: deterministic, fully observable through
`BPF_PROG_LOAD` and its log, instrumented, and with strong prior work
(Agni, Jitterbug, state embedding). But a same-shaped mirror means:
- a second verifier of more than 20k lines, whose state (explored-state
  lists, register and stack abstract states, precision backtracking) is
  neither small nor stable;
- among the most frequently rewritten code in the kernel;
- a config case.

Prior work targets its abstract domains (tnum and range arithmetic), which
can be checked far more cheaply in isolation than through a whole-verifier
mirror. Effort is 4 to 6 WU with a weak proof fit (C9 = 1).

io_uring is a near second to avoid, for its dispatch model: io-wq kthreads
and `task_work` sit outside the instruments.
