# Offline development proposal — 2026-09-20

**Recommended arrangement:** keep project tools, source checkouts, documentation,
caches, kernel images, and experiment data inside this repository directory.
Allow read/execute access to a recorded host system toolchain and runtime as the
initial platform dependency. Run the Linux behavioral oracle in a QEMU system
guest using TCG software emulation. Use the outer development sandbox to restrict
QEMU's host access as well as the build processes.

This is the original preparation specification and pre-staging audit. Staging
has since been completed locally; see [offline usage and validation](offline-usage.md)
for the implemented environment. The audit table below records the starting state.

**What the environment audit established**

| Item | Observed state | Consequence |
| --- | --- | --- |
| Host | Ubuntu 24.04.4, x86-64; running kernel `7.0.0-31-generic` | The host kernel is not the proposed behavioral oracle |
| Capacity | 32 reported CPUs, about 125 GiB RAM, about 553 GiB free | Capacity appears sufficient; no build-throughput measurement yet |
| Lean | 4.33.1 installed under `/home/dev/.elan/toolchains/leanprover--lean4---v4.33.1`; about 2.9 GiB | Copy the complete distribution into `.tools/lean`; a symlink to the home directory will not make it local |
| Lean validation | `import Std`, a small checked theorem, native executable build and execution succeeded | Core/Std-only development is viable with the existing distribution |
| C validation | GCC 13.3.0; static C compilation and execution succeeded | A small guest runner can initially use existing GCC/glibc without a musl dependency |
| Other tools | Python 3.12.3, Git 2.43.0, Make, binutils, Clang/LLVM 19.1.1, BusyBox static, cpio, bc, xz, zstd | Most basic harness and initramfs tooling is already present |
| Missing build packages | `bison`, `flex`, `libelf-dev`, `libssl-dev` | Stage these and their dependency closure; validate by actually building the selected kernel |
| QEMU | No `qemu-system-x86_64` or `qemu-system-aarch64` found | Provision the x86 system emulator, dependencies, firmware and data files |
| Kernel source | Only distribution headers found under `/usr/src`; no full source in the repository | Fetch the complete pinned tree including headers, scripts, documentation and licenses |
| Host KVM | `/dev/kvm` not present | Select TCG explicitly; do not require nested virtualization |
| Sandbox facilities | nono 0.77.0 and bubblewrap installed | Their presence does not establish that the proposed guest works under a final profile |
| Network | Default shell could not resolve kernel.org; the explicitly escalated network tool succeeded | Online preparation is possible through that tool path; ordinary commands are already restricted |

The initial `elan show` also attempted a moving `stable` lookup and encountered
an `Operation not permitted` failure. The nono diagnostic reported no grant for
`/home/dev/.elan`. Treat this as an OS sandbox boundary. The installed compiler
itself successfully built the independent probe. Use an exact, local toolchain
for the offline workflow rather than depending on this global installation.

If a future nono profile genuinely requires an additional external path, the two
supported routes are a one-session restart with `nono run --allow /needed/path
-- ...`, or a derived profile drafted under `~/.config/nono/profile-drafts` and
reviewed with `nono profile promote`. No profile was changed during this review.
The proposed local bundle should avoid needing a grant to the global Lean cache.

**Versions and source pins**

These are proposed choices, not requirements to follow the latest releases.
Full commits were resolved using upstream Git refs on 2026-09-20. Machine-readable
values and unresolved build artifacts are in [resource-proposal.json](resource-proposal.json).

| Component | Proposed pin | Reason |
| --- | --- | --- |
| Lean | `v4.33.1`, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` | Already installed and successfully compiled here; use bundled Std/Lake |
| Linux | `v6.12.110`, commit `fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c` | A fixed release in the maintained 6.12 longterm series; inspected FD/eventfd source is manageable |
| Firecracker | `v1.17.0`, commit `95f868c8e345b1cc8faccd1a3c910b4989dc3f58` | Source and policy reference; building or running it is deferred |
| Syzkaller | `853b104bb454141a5b0fc0e4218ec78e9f34ffb1` | Source snapshot for descriptions and later generator/minimizer reuse; not yet integration-tested |
| Kernel C compiler | GCC 13.3.0, Ubuntu package `13.3.0-6ubuntu2~24.04.1` | Installed; record binutils, libc, flags and full package identities too |
| QEMU | Initial packaging candidate `1:8.2.2+ds-0ubuntu1.18` from the local Ubuntu index | Resolve availability, dependencies and file hashes during provisioning; this candidate has not been installed |

Linux's longterm status is documented by [kernel.org](https://www.kernel.org/releases.html).
The Linux archive endpoint responded with a size of 148,552,636 bytes (about
142 MiB); that archive was not downloaded. Commit identity and archive checksums
must both be recorded. Retain upstream signatures/verification results where
available; a checksum recorded after download alone is only an integrity check.

**Resources to stage while network access is available**

| Resource | Required for the first loop | Preparation |
| --- | --- | --- |
| Lean distribution | Yes | Complete binaries, libraries, Std sources, `.olean` files, bundled native compiler/linker; exact `lean-toolchain` file |
| Linux source and build outputs | Yes | Full pinned tree; full resolved `.config`; patch list; `bzImage`, unstripped `vmlinux`, `System.map`, build logs and hashes |
| QEMU | Yes | Executable, shared-library closure, firmware/data directory; explicit search paths if extracted into `.tools` |
| C/build tools | Yes | GCC/binutils/libc headers and static libraries, Make, bc, bison, flex, libelf/OpenSSL development packages, cpio and compression tools |
| Guest userspace | Yes | Static BusyBox and static runner; minimal initramfs `/init`, device setup, proc/sys/debugfs mounts |
| Python | Yes | Standard-library-only generator, comparator and shrinker; preserve interpreter/platform version |
| Reference material | Yes | Pinned kernel Documentation, relevant man-pages, Lean manual and tool sources, QEMU manual, source/license records |
| Firecracker source | Reference only | Both architecture policies, security/design/jailer/seccompiler documentation, build feature information |
| Syzkaller source | Reference initially | Descriptions, generated target data or reproducible generation inputs, documentation; preserve full checkout for later integration |
| Go and modules | Before adopting syzkaller tooling | The inspected `go.mod` requires Go 1.26.0; stage a compatible exact Go release and selected tools' complete module dependencies, then prove an offline build |
| Editor and Lean LSP tools | Useful | Local editor extension and Lean server; any MCP helper's Python environment/wheels/binaries must also be staged if used inside the sandbox |
| mathlib, SMT/proof tools, Firecracker Rust build | Deferred | Add only when a specific milestone needs them; each addition needs pinned transitive sources and an offline build test |

Avoid a global package manager in the normal development loop. Start with a
recorded, read-only Ubuntu toolchain plus local project-specific tools. During
provisioning, archive the required `.deb` packages and dependency closure so the
baseline can be recreated. Installing packages is one option outside the sandbox;
extracting them locally requires correct loader, library, header and data paths,
not merely adding one directory to `PATH`.

If access to host system directories must also disappear, provision a complete
local userspace/sysroot or preloaded container image and validate its launcher
under the intended sandbox. This is a separate portability milestone. A Docker
socket or an untested assumption that nested user namespaces work is not a local
dependency strategy.

Budget **20–40 GiB** initially for source, Lean, emulator dependencies, a kernel
build with debug information, caches and a bounded corpus. This is a planning
allowance, not a measured bundle size. Debug builds and unbounded coverage logs
can grow substantially; retain minimized traces and compress archived reports.

**Proposed directory and access layout**

```text
.tools/lean/                 complete pinned Lean distribution
.tools/qemu/                 emulator and required runtime/data files
.deps/linux/                complete Linux source at the selected commit
.deps/firecracker/          pinned source/policies
.deps/syzkaller/            pinned source/descriptions
.deps/docs/                 local manuals and references
.deps/downloads/            archives, packages, signatures, checksums
.cache/                    project-local tool caches and temporary files
.artifacts/kernel/          out-of-tree kernel build and resolved configuration
.artifacts/guest/           initramfs, runner, boot logs
.artifacts/runs/            disposable run directories and raw observations
Leanux/                    modeled semantics and later proofs
harness/                   generator, C runner, comparator and minimizer
correspondence/             source maps and named abstractions
corpus/                    curated regression and critic traces
```

Track recipes, manifests, configuration, semantics, source-map records and small
regressions in Git. Keep downloaded tools and bulk outputs ignored but present
on disk. Ignoring a directory does not provision it. Avoid partial clones that
fetch missing objects on demand or Git LFS pointers without their local content.

The sandbox needs read/execute access to local dependencies and the declared host
runtime/toolchain; writes to project build/cache/run directories; process creation,
pipes, signals, and the executable-memory mappings needed by TCG. It needs a small
host `/dev` and `/proc` allowance as established by the smoke test. It should not
need host debugfs, host KVM, mounts, a container daemon, SSH, or a virtual NIC.
Permissions for mounts and debugfs inside the guest are guest-kernel operations.
An editor/LSP may need a local socket even when the test harness uses pipes.

Configure `TMPDIR`, `XDG_CACHE_HOME`, `ELAN_HOME`, and Lake's cache/config paths
under `.cache`. Invoke `.tools/lean/bin/lake` directly with an exact
`lean-toolchain`. For the inspected Lake version, `--no-cache` disables remote
build-cache downloads and `--keep-toolchain` prevents automatic toolchain changes.
Neither makes missing source dependencies available: use bundled Std initially,
then vendor or prefetch all Lake packages before adding them.
[Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)

If Go is introduced, keep its module/build caches local, set `GOTOOLCHAIN=local`,
and test with `GOPROXY=off` after provisioning. If Rust is introduced, vendor
crates and use locked offline builds. Remote theorem search is optional; local
Lean diagnostics and proof checking must work without it.

If syzkaller integration is planned during the first offline work period, stage
Go and its module closure now as well. Deferring that download means deferring
integration until another explicitly network-enabled provisioning session.
This proposal assumes build/test subprocesses are offline while agent
orchestration runs outside that boundary. A completely disconnected machine
would additionally need locally provisioned model inference for an agent loop.

**Linux oracle design**

Use QEMU system emulation with explicit `-accel tcg`, one vCPU, a pinned x86-64
machine/CPU, fixed RAM, direct kernel/initramfs boot, serial pipes, `-nic none`,
and no host filesystem shares. Fix the kernel command line and save the complete
emulator invocation. Firmware is still a dependency on x86. TCG performance and
compatibility with the final sandbox must be measured, not assumed.
[QEMU invocation reference](https://www.qemu.org/docs/master/system/invocation.html)

The guest supervisor mounts debugfs and prepares a task-local KCOV buffer; the
worker enables coverage in the executing task. Separate setup, transport and
coverage syscalls from the observed test operation. Normalize coverage addresses
against the matching build, preferably beginning with guest KASLR disabled. Keep
coverage instrumentation fixed within an experiment; compare selected cases
against an uninstrumented build later.
[KCOV setup and collection](https://docs.kernel.org/dev-tools/kcov.html)

Begin from a small kernel configuration with initramfs, ELF, serial console,
eventfd, proc/sysfs, debugfs, KCOV, and DWARF debug information. Save the complete
resolved configuration, not just a fragment. Add KCOV comparisons after basic
PC collection works. Disable unnecessary modules and devices; explicitly record
LSMs, seccomp state, mitigations, preemption and other relevant configuration.

Run each trace in a fresh child with a fixed inherited FD inventory, credentials,
resource limits and signal disposition. Reserve runner/coverage descriptors and
include them in the allocator's initial state. Restrict generated descriptor
arguments to the test domain. Use bounded allocated I/O buffers and nonblocking
operations. Apply a parent watchdog; save a timeout as a separate result.

The first transport can embed a batch of traces in an initramfs and emit framed
observations over serial, avoiding SSH and sockets entirely. A persistent guest
can later accept batches over serial with one fresh child per trace. Reboot on
guest-level failure; record kernel-global state assumptions between traces.

A container on the host would still use the host kernel. QEMU user-mode emulation
would also route syscalls into the host kernel. Neither provides the pinned
kernel oracle required here. QEMU system emulation executes the selected Linux
kernel, but it remains host software subject to the outer sandbox.
[QEMU security model](https://www.qemu.org/docs/master/system/security.html)

**Provisioning order and the offline acceptance test**

1. Resolve/download the proposed sources and tool packages into local directories;
   verify provenance and hashes. Copy the installed Lean distribution or obtain
   the same official release. Record all package versions and licenses.
2. Build a minimal kernel and initramfs. Save source commit, configuration, compiler
   identity, build inputs and output hashes. Boot QEMU under the current environment
   and establish serial communication plus one KCOV observation.
3. Create the project wrappers and source/build manifest. Run the same boot under
   the intended sandbox profile with all network access denied. Confirm that the
   profile also rejects out-of-scope host writes and network attempts.
4. In a fresh disposable build directory inside the project, rebuild the Lean
   probe, static C runner, initramfs and kernel without global home caches. Start
   from staged source dependencies and remove only disposable generated outputs.
   Record all unexpected path accesses; adjust the declared runtime contract.
5. Run hand-written traces, symbolize KCOV against the saved `vmlinux`, restart
   the guest and reproduce results. Treat this complete exercise as the gate for
   calling the environment offline-ready.

The included `scripts/probe-toolchains.py` covers only the Lean/native-C portion
of step 4. It was exercised using the installed Lean 4.33.1 distribution, and both
executables ran successfully. It is not a sandbox launcher or a network policy.
At the time of this initial audit, no complete offline acceptance test had been
performed. The subsequent results are recorded in [offline-usage.md](offline-usage.md).

All future experiment manifests should include the Lean-ux revision and dirty
patch, source commits, kernel config/build hashes, compiler/binutils/libc versions,
runner and initramfs hashes, QEMU version/machine/CPU/arguments, guest credentials
and resource limits, trace/schema/normalizer versions, and random seed. Changing
any of these creates a new experiment identity.
