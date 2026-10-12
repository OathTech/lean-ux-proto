# Staged offline development

Dependencies for the first x86-64 prototype are staged in this repository.
Use the existing nono agent session for confinement and `scripts/in-bundle`
to select the local tools. No global packages, editor settings, or shared nono
profiles need changing.

```sh
scripts/in-bundle                              # shell with local tools
scripts/in-bundle lean --version
scripts/in-bundle python3 scripts/probe-toolchains.py
scripts/in-bundle scripts/build-kernel
scripts/in-bundle python3 scripts/check-guest.py
```

The runner configures compiler sysroots, backend executables, library lookup,
QEMU firmware, Python packages and project-local caches. It performs no mounts,
creates no namespaces, and does not grant or remove sandbox permissions. Its
name is retained for compatibility with the original preparation scripts.
It does not itself block networking or make `.tools` read-only; those permissions
are determined by the enclosing nono profile. The default agent profile permits
selected API/download domains.

The host bootstrap is Linux x86-64, glibc 2.39 or newer, `/bin/sh`, Python 3.9+
and nono. System interpreters in absolute script shebangs remain host runtime
dependencies. The native loader and glibc stay paired with the host; additional
libraries, compilers, target C headers/libraries, Lean, Go and QEMU come from the
staged bundle. No host development packages or global language caches are needed.

## Bundle contents

| Location | Contents |
| --- | --- |
| `.tools/lean` | Lean 4.33.1, Lake/Std, compiled libraries and sources |
| `.tools/go` | Go 1.26.5 |
| `.tools/sysroot` | 222 Ubuntu packages: GCC/G++ 13.3, binutils, LLVM/Clang/LLD/clang-format 19, Python 3.12, kernel build tools, QEMU 8.2.2, firmware, BusyBox and libraries |
| `.tools/lean-lsp` | Lean LSP MCP 0.29.0 and 41 locked Python distributions |
| `.deps/linux` | Linux v6.12.110 source and documentation |
| `.deps/firecracker` | Pinned v1.17.0 source and architecture policies |
| `.deps/syzkaller` | Pinned source, generated descriptions, host tools and executor |
| `.deps/go-mod` | Complete local module store for syzkaller; retain for offline builds |
| `.deps/docs` | Lean reference manual, QEMU/KCOV references and syscall manual pages |
| `.deps/downloads` | Source/package archives, toolchain snapshots and upstream metadata |
| `.cache` | Disposable caches, local tool-wrapper links and library links |
| `.artifacts` | Builds, guest images, coverage, probes and validation logs |

The Lean manual is the 4.33.0 reference for the 4.33 release series; the compiler
is 4.33.1. Open `.deps/docs/lean-reference/index.html` locally. Kernel,
Firecracker and syzkaller documentation is also in each source tree.

Go uses four execution threads; the kernel build defaults to four jobs, and
syzkaller's make driver runs serially. Go proxy and checksum-server downloads
are disabled. Syzkaller uses its pinned revision/date rather than Go's automatic
Git stamping of the enclosing repository. No global Git configuration is needed
for those archive builds.

## Lean diagnostics and guest details

```sh
scripts/lean-lsp /absolute/path/to/a/Lean/project/inside/this/repository
```

This starts the local stdio MCP helper with remote search tools disabled. It
does not register anything globally. `scripts/lean-lsp-python` uses the staged
Python interpreter and copied package directory without modifying the original
venv. Lean's `lake serve` is also available through `scripts/in-bundle`. The
upstream MCP helper can emit an asyncio cleanup warning (`Event loop is closed`)
on exit after both diagnostic responses have completed successfully.

The kernel recipe records its configuration in `kernel/config-x86_64` and
normally builds in `.artifacts/kernel`. `LEANUX_KERNEL_BUILD` can select another
directory under `.artifacts`; use the same value for `check-guest.py`.
The guest uses QEMU TCG, one CPU, 256 MiB RAM and a fixed `pc-i440fx-8.2` machine.
It has no NIC, KVM, shared host filesystem or host disk. All experimental kernel
execution stays in QEMU. A small C program under `harness/probes` validates the
setup; it is not the eventual oracle harness.

## Preservation and deferred dependencies

Keep `.deps`, `.tools`, and the locks when moving offline. Keeping `.artifacts`
saves rebuilding and preserves evidence. A Git clone alone does not contain the
ignored dependency bundle. `.cache` is disposable; discard it when relocating
the workspace because its generated tool links contain absolute paths.
`.deps/go-mod` is not disposable.

`dependencies/*.lock.json` records versions, hashes and provenance. Ubuntu
checksums came from the existing package index; the Linux archive matched
kernel.org's checksum. Firecracker and syzkaller use commit-addressed archives.
Lean, Go and MCP are independent snapshots of existing local installations.
Licenses remain with the packages and sources.

`python3 scripts/restore-toolchains.py` can restore missing Lean/Go/MCP directories
from cached snapshots. It needs host Python, tar and zstd and leaves existing
directories untouched. The staging script can also reuse cached downloads.
Restoring dependencies is separate from normal builds.

Mathlib, SMT tools, building Firecracker itself, KVM and an AArch64 guest/cross-libc
setup remain deferred. Firecracker's reference source is present; its Rust
build dependencies are not included.
