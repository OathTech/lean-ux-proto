# First prototype proposal — 2026-09-20

**Historical proposal:** the current [objectives](project-objectives.md) and
[execution plan](prototype-plan.md) incorporate the subsequent discussion of
computational correspondence, local stepping proofs, evaluator integrity, and
autonomous parallel work. They supersede the implementation sequence below;
the source observations and semantic slice details remain useful context.

**Recommendation:** build a sequential file-descriptor/eventfd experiment on
Linux v6.12.110, using Lean 4.33.1 and an x86-64 QEMU guest with software
emulation. Establish source correspondence with the first implementation. Add
coverage, minimization, and adversarial repair tests before expanding the syscall
surface. Preserve AArch64 as the next target for virtualization work.

This reviews [the brainstorming note](2026-09-19-rough-plan.md). It proposes
implementation work; it does not claim that a kernel model or simulation proof
already exists. [The setup proposal](offline-development.md) specifies the
resources to prepare before offline development.

**What to keep from the plan**

The central experiment is well chosen: use stateful differential tests to discover
which Linux distinctions a useful abstraction must retain. The combination of
executable semantics, explicit source correspondence, minimized counterexamples,
and eventual local simulation obligations is much stronger than syscall return
value matching alone. Keeping KVM abstract and treating compromise of the VMM as
an initial condition also gives the eventual security question a clear purpose.

The first success criterion should be one convincing mismatch-to-repair cycle
with a source-grounded explanation and falsifying neighbor tests. Syscall count
and an impressive agreement percentage would be poor early targets.

**Changes needed before implementation**

1. **Start correspondence immediately.** Sections 7 and 24 disagree about when
   this begins. Even the first `dup` implementation needs a record of its Linux
   counterpart, represented fields, assumptions, and omitted mechanisms.
2. **Keep FD numbers observable.** `dup` chooses the lowest unused descriptor;
   `dup3` names a destination. Reuse, aliasing, descriptor flags, and file status
   flags must survive comparison. Start with a fixed inherited FD layout and
   compare descriptor numbers literally. Rename internal object identities only
   with a relation that preserves equality and aliasing.
   [Linux dup documentation](https://man7.org/linux/man-pages/man2/dup.2.html)
3. **Define “sealed” as a new, explicit configuration.** The inspected
   Firecracker v1.17.0 x86-64 policy permits `open`, `io_uring_*`, and `recvmsg`
   in the VMM thread. Initial FDs alone are therefore not an adequate authority
   inventory. Later work must account for namespace-visible paths, credentials,
   mount state, received FDs, asynchronous operations, and permitted resource
   creation, or explicitly exclude them through the chosen policy and environment.
   Normal application traces do not bound what compromised code can request.
   [Pinned Firecracker policy](https://github.com/firecracker-microvm/firecracker/blob/95f868c8e345b1cc8faccd1a3c910b4989dc3f58/resources/seccomp/x86_64-unknown-linux-musl.json)
4. **Make the initial sequential restriction explicit.** One thread, no signal
   injection, nonblocking eventfds, and no external kernel producers are useful
   experimental conditions. They do not justify later treating a whole syscall
   as atomic under concurrency. Locks, RCU, reference lifetimes, and the Linux
   memory model will need separate refinement obligations.
5. **Separate disagreement from infrastructure failure.** Unsupported inputs,
   timeouts, guest crashes, allocation-pressure failures, malformed output, and
   missing coverage are distinct outcomes. None counts as behavioral agreement.
   Capture return value and output bytes; record errno only on syscall failure.
6. **State the proof limit precisely.** Forward simulation with matching effects
   could transfer suitable safety properties under explicit assumptions. It does
   not automatically transfer liveness, timing, or confidentiality hyperproperties.
   C semantics, undefined behavior, assembly, compiler assumptions, and concurrency
   remain source-side research work. A lemma about an idealized Lean encoding must
   be labelled as such.
7. **Stage syzkaller adoption.** Preserve its pinned source and descriptions now.
   Use a small typed trace format for the first loop; then evaluate reuse of its
   generator and minimizer. Its workload machinery is relevant, but adapting
   execution and observation is still project work.
   [Syzkaller description format](https://github.com/google/syzkaller/blob/853b104bb454141a5b0fc0e4218ec78e9f34ffb1/docs/syscall_descriptions.md)

**The first semantic slice**

Use `eventfd2`, `dup`, `dup3`, `close`, `read`, `write`, and the `F_GETFD`,
`F_SETFD`, and `F_GETFL` variants of `fcntl`. Creation always requests nonblocking
mode; test ordinary and semaphore eventfds. Defer changing nonblocking mode,
epoll, mmap, fork/exec, signals, concurrent calls, and arbitrary user pointers.
`dup` is a methodology probe, not a claim that the selected Firecracker policy
permits it after sealing.

Specify the x86-64 syscall ABI in the trace contract: argument widths, signed
descriptor/error handling, and little-endian I/O bytes. In particular, eventfd
creation takes a 32-bit initial value while its accumulated counter is 64-bit.
The C runner should issue the intended syscalls without automatic retries that
could hide an observed failure.

Trace arguments must distinguish a result reference from a literal descriptor
number. A stale reference retains its original number, so subsequent reuse can
change what it names. Failed producers and invalid references need an explicit
trace validity rule. The generator must produce meaningful negative tests without
accidentally targeting its transport or coverage descriptors.

Model this ownership chain:

```text
task_struct.files
    -> files_struct / fdtable
         fd number -> struct file
                         -> file.private_data -> eventfd_ctx
```

| Linux component | Initial Lean counterpart | Information to retain |
| --- | --- | --- |
| `files_struct`, `fdtable` | `Leanux.FS.Files`, `FDTable` | Slot membership, close-on-exec bits, allocation cursor, descriptor limit |
| `struct file` | `Leanux.FS.File` | Shared object identity, status flags, object kind, logical ownership |
| `eventfd_ctx` | `Leanux.FS.Eventfd.Ctx` | 64-bit counter and semaphore mode |
| `alloc_fd`, `fd_install`, `file_close_fd_locked` | Corresponding helpers in `Leanux/FS/File.lean` | Allocation, installation, and removal as separate transitions/helpers |
| `ksys_dup3`, `do_dup2` | Corresponding duplication helpers | Validation order, target replacement, shared file identity |
| `do_eventfd`, `eventfd_read`, `eventfd_write`, `eventfd_ctx_do_read` | Helpers in `Leanux/FS/Eventfd.lean` | Creation, counter transitions, error ordering |

These names were checked against the proposed pinned
[file implementation](https://github.com/gregkh/linux/blob/fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c/fs/file.c),
[FD table definitions](https://github.com/gregkh/linux/blob/fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c/include/linux/fdtable.h),
and [eventfd implementation](https://github.com/gregkh/linux/blob/fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c/fs/eventfd.c).
Resolve syscall wrappers and remaining supporting structures against the full
checkout before declaring the map complete. Do not equate Linux's raw reference
counts with a count of open descriptors: temporary and kernel-held references
need an explicit abstraction.

An instructive source detail: this eventfd implementation accepts a read buffer
of at least eight bytes but requires writes to be exactly eight bytes. It also
updates the counter before the read's final user-memory copy, so an error does
not universally imply unchanged state. Initially use valid allocated buffers;
record faulting copies as unsupported and retain this case for later expansion.
These are source findings, not results from executing the pinned kernel.

**First distinguishing trace**

```text
a = eventfd2(0, NONBLOCK | CLOEXEC)
b = dup(a)
write(a, u64(5), 8)             -> 8
close(a)                       -> 0
read(b, valid_buffer, 8)        -> 8, bytes encoding 5
read(b, valid_buffer, 8)        -> EAGAIN
```

The expected behavior follows from the shared open file description and eventfd
counter semantics; it must be confirmed against the pinned executable.
[Eventfd documentation](https://man7.org/linux/man-pages/man2/eventfd.2.html)

Useful neighbors include a second independent eventfd; reads through each alias;
closing the duplicate first; reusing the freed descriptor; `dup3` replacing a live
target; invalid and equal descriptors; descriptor flag differences; semaphore
mode; lengths 0, 7, 8, 9, and 16; and counter values around saturation. Check
post-error state through a subsequent operation. Fix resource limits in the
fixture and add descriptor-exhaustion cases deliberately.

**Implementation sequence and completion gates**

| Step | Concrete deliverable | Completion gate |
| --- | --- | --- |
| 0. Prepare offline development | Local tools/sources, resolved manifest, kernel config, built kernel and initramfs, boot wrapper | Under the intended sandbox with network denied, clean-build Lean and C, rebuild the kernel, boot the guest, and collect symbolized KCOV from one operation |
| 1. Establish the experiment contract | Versioned trace and observation schemas, fixed FD fixture, raw-syscall C guest runner, 10–20 hand-written traces | Repeat each trace in fresh children; compare raw return values, error codes and output bytes; retain complete run identity and classify failures |
| 2. Build the Lean mirror | `Leanux/FS/File.lean`, `Eventfd.lean`, state types, executable runner, initial correspondence/abstraction records | Hand-written traces agree; every modeled helper has a source record; another reader can follow the ownership and control-flow map |
| 3. Generate and minimize | Seeded Python generator/comparator and dependency-aware shrinker; later syzkaller adapter | At least 1,000 bounded generated traces run reproducibly; an injected aliasing bug is detected and reduced to a small reproducer |
| 4. Test repair quality | Source-grounded repair, separate adversarial corpus, per-operation KCOV and Lean branch reports | A deliberately over-specialized repair fails unseen neighboring traces; a principled repair passes them without changing the oracle |
| 5. Add a proof foothold | Explicit `relateFiles` sketch and a Lean-checked local invariant | Prove that duplicating a descriptor preserves shared file identity, or closing one alias preserves lookup through another, under stated invariants and without `sorry` |

Step 0 should resolve the riskiest environment questions before sustained model
work. Step 3's trace count is an engineering gate, not evidence of completeness.
Measure throughput and branch discovery before choosing a larger fuzzing target.

Each mismatch bundle should contain the input and seed, raw observations, first
divergence, minimized trace, Linux/Lean coverage, source and artifact hashes,
assumptions, and the eventual regression. The minimizer preserves the mismatch
class and producer dependencies; it must not reduce a semantic mismatch into a
timeout or parser error.

KCOV provides instrumented execution addresses, not a complete call graph or an
independent structural proof. Preserve the matching unstripped `vmlinux`, compiler
configuration, and symbolization tools. Report coverage of identified source
branches and explicitly note uninstrumented regions.
[Kernel KCOV documentation](https://docs.kernel.org/dev-tools/kcov.html)

For the repair experiment, freeze the oracle, trace schema, and normalization at
a recorded revision while the builder changes semantics. A separate critic task
produces executable tests and checks the source explanation. An oracle bug requires
an explicit, separately reviewed correction and replay of the corpus. Neither
agent is a trusted proof component.

The first invariant should concern aliasing and object authority in this slice.
If eventfd creation remains in the transition set, newly allocated objects must
be classified as freshly owned authority; “all objects existed initially” would
be false. A Firecracker confinement claim comes only after the allowed operations
and environment form a closed, explicitly justified security boundary.
